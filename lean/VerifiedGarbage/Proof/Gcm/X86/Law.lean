module

public import VerifiedGarbage.Impl.Gcm.X86
public import VerifiedGarbage.Proof.Gcm.X86.Ghash
public import VerifiedGarbage.Proof.Gcm.Slots
public import VerifiedGarbage.Proof.Gcm.Spread32
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Gcm.X86.Lit
public import VerifiedGarbage.Proof.Gcm.X86.Lanes
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Gcm.X86.Lit
meta import VerifiedGarbage.Proof.Gcm.X86.Ghash
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# GHASH with integer multiplications on x86 (32-bit)

Untrusted: everything here is checked by Lean. The blocks of the code but for
its loads of the arguments, `H`, `Y` and the data are run on an abstract
machine, the registers and the 64 words of `scratch` (`A`, `evalA`), which
the machine follows (`sound`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86

open VG VG.X86
open VG.Impl.Gcm.X86
open Polynomial (X)
open VG.Proof.Gcm.Spread (lp lp_xor keyW0 keyW1)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-! ## The abstract machine -/

structure A where
  g : Reg → BitVec 32
  m : Nat → BitVec 32
  x : XReg → BitVec 128

namespace A

def set (a : A) (d : Reg) (v : BitVec 32) : A := ⟨fun r => if r = d then v else a.g r, a.m, a.x⟩
def put (a : A) (k : Nat) (v : BitVec 32) : A := ⟨a.g, fun j => if j = k then v else a.m j, a.x⟩
def setX (a : A) (d : XReg) (v : BitVec 128) : A := ⟨a.g, a.m, fun r => if r = d then v else a.x r⟩
/-- Vector `j` of `scratch`. -/
def putV (a : A) (j : Nat) (v : BitVec 128) : A := ⟨a.g, fun k => if k / 4 = j then dword v (k % 4) else a.m k, a.x⟩
/-- The vector of words `4 j` to `4 j + 3`. -/
def vec (a : A) (j : Nat) : BitVec 128 := ofDwords (a.m (4 * j)) (a.m (4 * j + 1)) (a.m (4 * j + 2)) (a.m (4 * j + 3))

theorem g_set (a : A) (d : Reg) (v : BitVec 32) (r : Reg) : (a.set d v).g r = if r = d then v else a.g r := rfl
theorem m_set (a : A) (d : Reg) (v : BitVec 32) : (a.set d v).m = a.m := rfl
theorem g_put (a : A) (k : Nat) (v : BitVec 32) : (a.put k v).g = a.g := rfl
theorem m_put (a : A) (k : Nat) (v : BitVec 32) (j : Nat) : (a.put k v).m j = if j = k then v else a.m j := rfl

theorem x_set (a : A) (d : Reg) (v : BitVec 32) : (a.set d v).x = a.x := rfl
theorem x_put (a : A) (k : Nat) (v : BitVec 32) : (a.put k v).x = a.x := rfl
theorem g_setX (a : A) (d : XReg) (v : BitVec 128) : (a.setX d v).g = a.g := rfl
theorem m_setX (a : A) (d : XReg) (v : BitVec 128) : (a.setX d v).m = a.m := rfl
theorem x_setX (a : A) (d : XReg) (v : BitVec 128) (r : XReg) : (a.setX d v).x r = if r = d then v else a.x r := rfl
theorem g_putV (a : A) (j : Nat) (v : BitVec 128) : (a.putV j v).g = a.g := rfl
theorem x_putV (a : A) (j : Nat) (v : BitVec 128) : (a.putV j v).x = a.x := rfl
theorem m_putV (a : A) (j : Nat) (v : BitVec 128) (k : Nat) :
    (a.putV j v).m k = if k / 4 = j then dword v (k % 4) else a.m k := rfl
theorem vec_setX (a : A) (d : XReg) (v : BitVec 128) (j : Nat) : (a.setX d v).vec j = a.vec j := rfl

theorem vec_putV (a : A) (j : Nat) (v : BitVec 128) (i : Nat) : (a.putV j v).vec i = if i = j then v else a.vec i := by
  simp only [vec, m_putV, show 4 * i / 4 = i by omega, show (4 * i + 1) / 4 = i by omega, show (4 * i + 2) / 4 = i by omega,
    show (4 * i + 3) / 4 = i by omega, show 4 * i % 4 = 0 by omega, show (4 * i + 1) % 4 = 1 by omega,
    show (4 * i + 2) % 4 = 2 by omega, show (4 * i + 3) % 4 = 3 by omega]
  split
  · exact ofDwords_dword v
  · rfl

end A

/-- The word of `scratch` an operand is. -/
def slotOf (m : MemOp) : Option Nat :=
  if m.base = .ecx ∧ m.disp % 4 = 0 ∧ m.disp < 256 then some (m.disp / 4) else none

theorem slotOf_slot {k : Nat} (hk : k < 64) : slotOf (slot k) = some k := by
  rw [slotOf, slot, at_, ite_eq_left ⟨rfl, by show 4 * k % 4 = 0; omega, by show 4 * k < 256; omega⟩]
  exact congrArg some (Nat.mul_div_cancel_left k (by decide))

/-- The vector of `scratch` an operand is. -/
def vslotOf (m : MemOp) : Option Nat :=
  if m.base = .ecx ∧ m.disp % 16 = 0 ∧ m.disp < 256 then some (m.disp / 16) else none

theorem vslotOf_vslot {j : Nat} (hj : j < 16) : vslotOf (vslot j) = some j := by
  rw [vslotOf, vslot, at_, ite_eq_left ⟨rfl, by show 16 * j % 16 = 0; omega, by show 16 * j < 256; omega⟩]
  exact congrArg some (Nat.mul_div_cancel_left j (by decide))

def xopA (a : A) : XOp → Option A
  | .bin o d r => some (a.setX d (o.eval (a.x d) (a.x r)))
  | .shift o d n => some (a.setX d (o.eval (a.x d) n))
  | .pshufd d r o => some (a.setX d (shufDwords (a.x r) o))
  | .pshuflw d r o => some (a.setX d (shufLowWords (a.x r) o))
  | .pshufhw d r o => some (a.setX d (shufHighWords (a.x r) o))
  | .movd d r => some (a.setX d ((0 : BitVec 96) ++ a.g r))
  | _ => none

def srcA (a : A) : Src → Option (BitVec 32)
  | .reg r => some (a.g r)
  | .imm v => some v
  | .mem m => (slotOf m).map a.m

def stepA : Instr → A → Option A
  | .mov d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map (a.set d)
  | .alu .xor d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map fun v => a.set d (a.g d ^^^ v)
  | .alu .and d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map fun v => a.set d (a.g d &&& v)
  | .alu .add d s, a => if d = .ecx ∨ d = .esp then none else (srcA a s).map fun v => a.set d (a.g d + v)
  | .bswap d, a => if d = .ecx ∨ d = .esp then none else some (a.set d (bswap (a.g d)))
  | .shift .shr d n, a =>
    if (d = .ecx ∨ d = .esp) ∨ ¬ (1 ≤ n ∧ n ≤ 31) then none else some (a.set d (a.g d >>> n))
  | .shift .ror d n, a =>
    if (d = .ecx ∨ d = .esp) ∨ ¬ (1 ≤ n ∧ n ≤ 31) then none else some (a.set d ((a.g d).rotateRight n))
  | .mul r, a =>
    let p := (a.g .eax).toNat * (a.g r).toNat
    some ((a.set .eax (BitVec.ofNat 32 p)).set .edx (BitVec.ofNat 32 (p / 2 ^ 32)))
  | .store m r, a => (slotOf m).map fun k => a.put k (a.g r)
  | .xop op, a => xopA a op
  | .movdquLoad d m, a => (vslotOf m).map fun j => a.setX d (a.vec j)
  | .movdquStore m r, a => (vslotOf m).map fun j => a.putV j (a.x r)
  | _, _ => none

def evalA : List Instr → A → Option A
  | [], a => some a
  | i :: is, a => (stepA i a).bind (evalA is)

theorem evalA_append (l₁ l₂ : List Instr) (a : A) : evalA (l₁ ++ l₂) a = (evalA l₁ a).bind (evalA l₂) := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, evalA, Option.bind_assoc]
    exact congrArg _ (funext fun a' => ih a')

/-- What the machine's state is to the abstract one's: `s₀` is the state at
entry, whose memory outside `scratch` is unchanged. -/
structure Rel (s₀ : State) (s : State) (a : A) : Prop where
  g : s.gpr = a.g
  m : Slots32 s₀.mem s.mem ((sP s₀).setWidth 64) 64 a.m
  ecx : a.g .ecx = sP s₀
  esp : a.g .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x : s.xmm = a.x

/-- What of the state at entry the abstract machine's steps need. -/
structure Scr (s₀ : State) : Prop where
  mem : sR s₀ ∈ s₀.wr
  fit : (sP s₀).toNat + 256 ≤ 2 ^ 32

namespace Rel

variable {s₀ s : State} {a : A}

theorem set (h : Rel s₀ s a) {d : Reg} (hd : ¬ (d = .ecx ∨ d = .esp)) (v : BitVec 32) : Rel s₀ (s.setReg d v) (a.set d v) :=
  ⟨by funext r; show (if r = d then v else s.gpr r) = _; rw [h.g]; rfl, h.m,
    by rw [A.g_set, ite_eq_right (fun e => hd (.inl e.symm))]; exact h.ecx,
    by rw [A.g_set, ite_eq_right (fun e => hd (.inr e.symm))]; exact h.esp, h.rd, h.wr, h.x⟩

theorem flags (h : Rel s₀ s a) (c o z f : Option Bool) : Rel s₀ (s.setFlags c o z f) a :=
  ⟨h.g, h.m, h.ecx, h.esp, h.rd, h.wr, h.x⟩

theorem setX (h : Rel s₀ s a) (d : XReg) (v : BitVec 128) : Rel s₀ (s.setXmm d v) (a.setX d v) :=
  ⟨h.g, h.m, h.ecx, h.esp, h.rd, h.wr, by funext r; show (if r = d then v else s.xmm r) = _; rw [h.x]; rfl⟩

theorem vslot (h : Rel s₀ s a) (hw : Scr s₀) {m : MemOp} {j : Nat} (hj : vslotOf m = some j) :
    j < 16 ∧ s.ea m = (sP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) ∧
      InRegions s.wr ((sP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) 16 := by
  have hf := hw.fit
  rw [vslotOf] at hj
  split at hj
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases hj
    refine ⟨by omega, ?_, sR s₀, by rw [h.wr]; exact hw.mem, Offset.contains_base _ (by omega) (by omega)⟩
    rw [State.ea, h1, h.g, h.ecx]
    exact (addr_eq (by omega)).trans (by rw [show 16 * (m.disp / 16) = m.disp by omega])
  · cases hj

/-- A vector of `scratch`, as loaded. -/
theorem load128 (h : Rel s₀ s a) {j : Nat} (hj : j < 16) :
    s.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) 128 = a.vec j := by
  have hd : ∀ i < 4, dword (s.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) 128) i = a.m (4 * j + i) :=
    fun i hi => by
      rw [dword_readW _ _ hi, Offset.add_add, show 16 * j + 4 * i = 4 * (4 * j + i) by omega, h.m.get _ (by omega)]
  rw [← ofDwords_dword (s.mem.readW _ 128), hd 0 (by decide), hd 1 (by decide), hd 2 (by decide), hd 3 (by decide)]
  rfl

theorem store128 (h : Rel s₀ s a) {j : Nat} (hj : j < 16) (v : BitVec 128) :
    Slots32 s₀.mem (s.mem.writeW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (16 * j)) v) ((sP s₀).setWidth 64) 64
      (a.putV j v).m := by
  refine ⟨fun k hk => ?_, h.m.frame.writeW (List.mem_singleton.mpr rfl) v
    (Offset.contains_base _ (by omega) (by omega))⟩
  rw [A.m_putV]
  split
  · rename_i e
    rw [show 4 * k = 16 * j + 4 * (k % 4) by omega, ← Offset.add_add]
    exact readW_writeW128 _ _ _ (by omega)
  · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    exact h.m.get k hk

theorem slot (h : Rel s₀ s a) (hw : Scr s₀) {m : MemOp} {k : Nat} (hk : slotOf m = some k) :
    k < 64 ∧ s.ea m = (sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) ∧
      InRegions s.wr ((sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by
  have hf := hw.fit
  rw [slotOf] at hk
  split at hk
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases hk
    refine ⟨by omega, ?_, _, by rw [h.wr]; exact hw.mem, Slots32.contains (n := 64) _ (by omega) (by decide)⟩
    rw [State.ea, h1, h.g, h.ecx]
    exact (addr_eq (by omega)).trans (by rw [show 4 * (m.disp / 4) = m.disp by omega])
  · cases hk

theorem src (h : Rel s₀ s a) (hw : Scr s₀) {o : Src} {v : BitVec 32} (hv : srcA a o = some v) : readSrc s o = some v := by
  cases o with
  | reg r => rw [← hv]; simp only [readSrc, srcA, h.g]
  | imm _ => exact hv
  | mem m =>
    simp only [srcA, Option.map_eq_some_iff] at hv
    obtain ⟨k, hk, hv⟩ := hv
    obtain ⟨hk, he, r, hr, hc⟩ := h.slot hw hk
    rw [readSrc, State.load32, he, ite_eq_left ⟨r, List.mem_append_right _ hr, hc⟩, ← hv, h.m.get k hk]

end Rel

theorem step_sound {s₀ s : State} {a a' : A} (h : Rel s₀ s a) (hw : Scr s₀) (i : Instr) (hi : stepA i a = some a') :
    ∃ s', exec i s = some s' ∧ Rel s₀ s' a' := by
  unfold stepA at hi
  split at hi
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      exact ⟨_, by rw [show exec _ s = (readSrc s _).map _ from rfl, h.src hw hv]; rfl, h.set hd v⟩
  iterate 3
    · split at hi
      · cases hi
      · rename_i hd
        simp only [Option.map_eq_some_iff] at hi
        obtain ⟨v, hv, rfl⟩ := hi
        refine ⟨_, by rw [show exec _ s = (readSrc s _).bind _ from rfl, h.src hw hv]; rfl, ?_⟩
        rw [h.g]
        exact (h.flags ..).set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  iterate 2
    · split at hi
      · cases hi
      · rename_i hd; cases hi
        obtain ⟨hd, hn⟩ := not_or.mp hd
        refine ⟨_, (ite_eq_left (Classical.not_not.mp hn)), ?_⟩
        show Rel s₀ (State.setReg _ _ _) _
        rw [h.g]; exact (h.flags ..).set hd _
  · cases hi
    refine ⟨_, rfl, ?_⟩
    simp only [execMul, h.g]
    exact ((h.flags ..).set (by decide) _).set (by decide) _
  · simp only [Option.map_eq_some_iff] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    obtain ⟨hk, he, hin⟩ := h.slot hw hk
    refine ⟨_, by rw [show exec _ s = State.store32 _ _ _ from rfl, State.store32, he, ite_eq_left hin], ?_⟩
    rw [h.g]
    exact ⟨rfl, h.m.store hk (by decide) _, h.ecx, h.esp, h.rd, h.wr, h.x⟩
  · unfold xopA at hi
    split at hi
    iterate 5
      · cases hi; refine ⟨_, rfl, ?_⟩; simp only [XOp.exec, h.x]; exact h.setX _ _
    · cases hi; refine ⟨_, rfl, ?_⟩; simp only [XOp.exec, h.g]; exact h.setX _ _
    · cases hi
  · simp only [Option.map_eq_some_iff] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    obtain ⟨hj, he, r, hr, hc⟩ := h.vslot hw hj
    refine ⟨_, by rw [show exec _ s = (State.load128 _ _).map _ from rfl, State.load128, he,
      ite_eq_left ⟨r, List.mem_append_right _ hr, hc⟩, h.load128 hj]; rfl, h.setX _ _⟩
  · simp only [Option.map_eq_some_iff] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    obtain ⟨hj, he, hin⟩ := h.vslot hw hj
    refine ⟨_, by rw [show exec _ s = State.store128 _ _ _ from rfl, State.store128, he, ite_eq_left hin], ?_⟩
    rw [h.x]
    exact ⟨h.g, h.store128 hj _, h.ecx, h.esp, h.rd, h.wr, rfl⟩
  · cases hi

/-- The machine runs what the abstract machine runs. -/
theorem sound {s₀ : State} (hw : Scr s₀) {is : List Instr} {s : State} {a a' : A}
    (h : Rel s₀ s a) (he : evalA is a = some a') : WP isa (.block is) s fun s' => Rel s₀ s' a' := by
  induction is generalizing s a with
  | nil => cases he; exact WP.block_nil h
  | cons i is ih =>
    simp only [evalA, Option.bind_eq_some_iff] at he
    obtain ⟨a₁, h₁, h₂⟩ := he
    obtain ⟨s₁, e, r⟩ := step_sound h hw i h₁
    exact WP.block_cons_iff.mpr ⟨s₁, e, ih r h₂⟩

/-! ## Running blocks -/

def WA (is : List Instr) (a : A) (Q : A → Prop) : Prop := ∃ a', evalA is a = some a' ∧ Q a'

theorem WA.append {l₁ l₂ : List Instr} {a : A} {Q : A → Prop} (h : WA l₁ a fun a' => WA l₂ a' Q) :
    WA (l₁ ++ l₂) a Q := by
  obtain ⟨a₁, e₁, a₂, e₂, q⟩ := h
  exact ⟨a₂, by rw [evalA_append, e₁]; exact e₂, q⟩

theorem WA.mono {l : List Instr} {a : A} {Q R : A → Prop} (h : WA l a Q) (hq : ∀ a', Q a' → R a') : WA l a R := by
  obtain ⟨a', e, q⟩ := h; exact ⟨a', e, hq a' q⟩

/-- The machine runs what `WA` says. -/
theorem WA.sound {s₀ s : State} {a : A} {is : List Instr} {Q : A → Prop} (hp : Scr s₀) (h : Rel s₀ s a) (hw : WA is a Q) :
    WP isa (.block is) s fun s' => ∃ a', Rel s₀ s' a' ∧ Q a' := by
  obtain ⟨a', e, q⟩ := hw
  exact WP.mono (X86.sound hp h e) fun s' r => ⟨a', r, q⟩

/-- Registers other than `rs` are unchanged. -/
def Keeps (rs : List Reg) (a a' : A) : Prop := ∀ r, r ∉ rs → a'.g r = a.g r

theorem Keeps.trans {rs : List Reg} {a b c : A} (h₁ : Keeps rs a b) (h₂ : Keeps rs b c) : Keeps rs a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem Keeps.mono {rs rs' : List Reg} {a b : A} (h : Keeps rs a b) (hs : ∀ r ∈ rs, r ∈ rs') : Keeps rs' a b :=
  fun r hr => h r fun h' => hr (hs r h')

/-- Vector registers other than `rs`, the others and the words are unchanged. -/
structure VK (rs : List XReg) (a a' : A) : Prop where
  x : ∀ r, r ∉ rs → a'.x r = a.x r
  m : a'.m = a.m
  g : a'.g = a.g

theorem VK.trans {rs : List XReg} {a b c : A} (h₁ : VK rs a b) (h₂ : VK rs b c) : VK rs a c :=
  ⟨fun r hr => (h₂.x r hr).trans (h₁.x r hr), h₂.m.trans h₁.m, h₂.g.trans h₁.g⟩

theorem VK.mono {rs rs' : List XReg} {a b : A} (h : VK rs a b) (hs : ∀ r ∈ rs, r ∈ rs') : VK rs' a b :=
  ⟨fun r hr => h.x r fun h' => hr (hs r h'), h.m, h.g⟩

theorem VK.refl (rs : List XReg) (a : A) : VK rs a a := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem VK.setX {rs : List XReg} {a b : A} (h : VK rs a b) {r : XReg} (hr : r ∈ rs) (v : BitVec 128) :
    VK rs a (b.setX r v) := by
  refine ⟨fun q hq => ?_, h.m, h.g⟩
  have : q ≠ r := fun e => hq (e ▸ hr)
  rw [A.x_setX, ite_eq_right this]
  exact h.x q hq

/-- The writes of `VK`, then the fact before them. -/
macro "vk " h:term : tactic => `(tactic| ((repeat refine VK.setX ?_ (by first | decide | simp) _); exact $h))

/-- An equation the simplifier closed, or one by definition. -/
macro "eqn" : tactic => `(tactic| first | exact True.intro | rfl)

theorem VK.vec {rs : List XReg} {a b : A} (h : VK rs a b) (j : Nat) : b.vec j = a.vec j := by rw [A.vec, A.vec, h.m]

/-- Instructions that write no vector register. -/
def scalarI : Instr → Bool
  | .xop _ | .movdquLoad .. => false
  | _ => true

theorem stepA_x {i : Instr} {a a' : A} (hi : scalarI i = true) (h : stepA i a = some a') : a'.x = a.x := by
  unfold stepA at h
  split at h
  iterate 7
    · split at h
      · cases h
      · first
          | (cases h; rfl)
          | (simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl)
  · cases h; rfl
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  · cases hi
  · cases hi
  · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  · cases h

theorem evalA_x {is : List Instr} {a a' : A} (hi : is.all scalarI = true) (h : evalA is a = some a') : a'.x = a.x := by
  induction is generalizing a with
  | nil => cases h; rfl
  | cons i is ih =>
    simp only [evalA, Option.bind_eq_some_iff] at h
    obtain ⟨a₁, h₁, h₂⟩ := h
    rw [List.all_cons, Bool.and_eq_true] at hi
    exact (ih hi.2 h₂).trans (stepA_x hi.1 h₁)

theorem WA.x {is : List Instr} {a : A} {Q : A → Prop} (h : WA is a Q) (hi : is.all scalarI = true) :
    WA is a fun a' => Q a' ∧ a'.x = a.x := by
  obtain ⟨a', e, q⟩ := h; exact ⟨a', e, q, evalA_x hi e⟩

open Spread (c4 m4 meet4 mul4 mul32x mulW4 W4 up32 dn32 redW4 mul_words32 setWidth_c4 m4_append append_halves)

theorem mask_eq (r : Nat) : mask r = c4 r := rfl

/-! ## The product of two words -/

/-- `mul`'s result. -/
theorem mul_append (x y : BitVec 32) :
    BitVec.ofNat 32 (x.toNat * y.toNat / 2 ^ 32) ++ BitVec.ofNat 32 (x.toNat * y.toNat) =
      x.setWidth 64 * y.setWidth 64 := by
  have hp : x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' x.isLt y.isLt
  apply BitVec.eq_of_toNat_eq
  rw [toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by have := x.isLt; omega),
    Nat.mod_eq_of_lt (show y.toNat < 2 ^ 64 by have := y.isLt; omega)]
  generalize x.toNat * y.toNat = p at hp ⊢
  omega

/-- Class `i` by class `j`. -/
def cp4 (a b : BitVec 32) (i j : Nat) : BitVec 64 := (a.setWidth 64 &&& m4 i) * (b.setWidth 64 &&& m4 j)

/-- The classes of `w` are at `b`. -/
def Cls (a : A) (b : Nat) (w : BitVec 32) : Prop := ∀ j < 4, a.m (b + j) = w &&& c4 j

theorem part_ok (t i j : Nat) (ht : t < 7) (hi : i < 4) (hj : j < 4) (w k : BitVec 32) (a : A) (hw : Cls a 28 w)
    (hk : Cls a (4 * t) k) :
    WA (part t i j) a fun a' => a'.g .edx ++ a'.g .eax = cp4 w k i j ∧ Keeps [.eax, .edx] a a' ∧ a'.m = a.m := by
  simp only [WA, part, ld, wS, evalA, stepA, srcA, slotOf_slot (show 28 + i < 64 by omega),
    slotOf_slot (show 4 * t + j < 64 by omega), Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left', hw i hi, hk j hj]
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · rw [mul_append, setWidth_c4 _ hi, setWidth_c4 _ hj, cp4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem addPart_ok (a : A) :
    WA addPart a fun a' => a'.g .esi ++ a'.g .ebx = (a.g .esi ++ a.g .ebx) ^^^ (a.g .edx ++ a.g .eax) ∧
      Keeps [.ebx, .esi] a a' ∧ a'.m = a.m := by
  simp only [WA, addPart, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · exact Spread.xor_append' .. |>.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

abbrev cw : List Reg := [.eax, .edx, .ebx, .esi]

theorem and_append' (a b c d : BitVec 32) : ((a ++ b : BitVec 64) &&& (c ++ d : BitVec 64)) = (a &&& c) ++ (b &&& d) :=
  BitVec.and_append

theorem classSum_ok (t r : Nat) (ht : t < 7) (hr4 : r < 4) (w k : BitVec 32) (a : A) (hw : Cls a 28 w)
    (hk : Cls a (4 * t) k) :
    WA (classSum t r) a fun a' => a'.g .esi ++ a'.g .ebx = meet4 (w.setWidth 64) (k.setWidth 64) r &&& m4 r ∧
      Keeps cw a a' ∧ a'.m = a.m := by
  have hP : ∀ i j, i < 4 → j < 4 → ∀ b : A, b.m = a.m → WA (part t i j) b fun b' =>
      b'.g .edx ++ b'.g .eax = cp4 w k i j ∧ Keeps [.eax, .edx] b b' ∧ b'.m = a.m := by
    intro i j hi hj b hb
    exact (part_ok t i j ht hi hj w k b (by rw [Cls, hb]; exact hw) (by rw [Cls, hb]; exact hk)).mono
      fun b' ⟨e, g, m⟩ => ⟨e, g, m.trans hb⟩
  have hS : ∀ (i j : Nat), i < 4 → j < 4 → ∀ b : A, b.m = a.m → Keeps cw a b → WA (part t i j ++ addPart) b fun b' =>
      b'.g .esi ++ b'.g .ebx = (b.g .esi ++ b.g .ebx) ^^^ cp4 w k i j ∧ Keeps cw a b' ∧ b'.m = a.m := by
    intro i j hi hj b hb kb
    refine WA.append ((hP i j hi hj b hb).mono fun c ⟨e, g, m⟩ => (addPart_ok c).mono fun d ⟨e', g', m'⟩ => ⟨?_, ?_, m'.trans m⟩)
    · rw [e', e, g _ (by decide), g _ (by decide)]
    · exact kb.trans ((g.mono (by decide)).trans (g'.mono (by decide)))
  rw [show classSum t r = part t 0 (r % 4) ++ (([mv .ebx .eax, mv .esi .edx] : List Instr) ++ ((part t 1 ((r + 3) % 4) ++
    addPart) ++ ((part t 2 ((r + 2) % 4) ++ addPart) ++ ((part t 3 ((r + 1) % 4) ++ addPart) ++
    ([.alu .and .ebx (.imm (mask r)), .alu .and .esi (.imm (mask r))] : List Instr))))) by
      simp only [classSum, List.append_assoc]]
  refine WA.append ((hP 0 _ (by decide) (Nat.mod_lt _ (by decide)) a rfl).mono fun b ⟨e₁, g₁, m₁⟩ => ?_)
  refine WA.append (WA.mono (Q := fun c => c.g .esi ++ c.g .ebx = cp4 w k 0 (r % 4) ∧ Keeps cw a c ∧ c.m = a.m)
    ?_ fun c ⟨e₂, g₂, m₂⟩ => ?_)
  · simp only [WA, mv, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
      reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨e₁, fun r hr => ?_, m₁⟩
    have hg := (g₁.mono (by decide) : Keeps cw a b) r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false, hg]
  refine WA.append ((hS 1 _ (by decide) (Nat.mod_lt _ (by decide)) c m₂ g₂).mono fun d ⟨e₃, g₃, m₃⟩ => ?_)
  refine WA.append ((hS 2 _ (by decide) (Nat.mod_lt _ (by decide)) d m₃ g₃).mono fun e ⟨e₄, g₄, m₄⟩ => ?_)
  refine WA.append ((hS 3 _ (by decide) (Nat.mod_lt _ (by decide)) e m₄ g₄).mono fun f ⟨e₅, g₅, m₅⟩ => ?_)
  rw [e₄, e₃, e₂] at e₅
  simp only [WA, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set, mask_eq,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, m₅⟩
  · rw [m4_append hr4, ← and_append', e₅]; rfl
  · have hg := g₅ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false, hg]

/-! ### Splitting a word -/

theorem classStore_ok (b : Nat) (r : Reg) (j : Nat) (hb : b + j < 64) (a : A) :
    WA (classStore b r j) a fun a' => a'.m (b + j) = a.g r &&& c4 j ∧ (∀ k, k ≠ b + j → a'.m k = a.m k) ∧
      Keeps [.edx] a a' := by
  simp only [WA, classStore, mv, st, evalA, stepA, srcA, slotOf_slot hb, Option.map_some, Option.bind_some, A.g_set,
    A.m_set, A.m_put, mask_eq, reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ite_eq_right hk, fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [A.g_put, A.g_set, hq, ite_false]

theorem split_ok (b : Nat) (r : Reg) (hb : b + 3 < 64) (hr : r ≠ .edx) (a : A) :
    WA (split b r) a fun a' => Cls a' b (a.g r) ∧ (∀ k, k < b ∨ b + 4 ≤ k → a'.m k = a.m k) ∧ Keeps [.edx] a a' := by
  have hr' : r ∉ [Reg.edx] := by simp [hr]
  rw [split, List.append_assoc, List.append_assoc]
  refine WA.append ((classStore_ok b r 0 (by omega) a).mono fun a₀ ⟨e₀, m₀, g₀⟩ => ?_)
  refine WA.append ((classStore_ok b r 1 (by omega) a₀).mono fun a₁ ⟨e₁, m₁, g₁⟩ => ?_)
  refine WA.append ((classStore_ok b r 2 (by omega) a₁).mono fun a₂ ⟨e₂, m₂, g₂⟩ => ?_)
  refine (classStore_ok b r 3 (by omega) a₂).mono fun a₃ ⟨e₃, m₃, g₃⟩ => ⟨fun j hj => ?_, fun k hk => ?_, ?_⟩
  · have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rw [m₃ _ (by omega), m₂ _ (by omega), m₁ _ (by omega), e₀]
    · rw [m₃ _ (by omega), m₂ _ (by omega), e₁, g₀ _ hr']
    · rw [m₃ _ (by omega), e₂, g₁ _ hr', g₀ _ hr']
    · rw [e₃, g₂ _ hr', g₁ _ hr', g₀ _ hr']
  · rw [m₃ k (by omega), m₂ k (by omega), m₁ k (by omega), m₀ k (by omega)]
  · exact g₀.trans (g₁.trans (g₂.trans g₃))

/-- The sum of the words `ks`. -/
def sumOf (m : Nat → BitVec 32) : List Nat → BitVec 32
  | [] => 0
  | k :: ks => ks.foldl (fun v k => v ^^^ m k) (m k)

theorem xors_ok (ks : List Nat) (hk : ∀ k ∈ ks, k < 64) (a : A) :
    WA (ks.map (xorM .eax)) a fun a' => a'.g .eax = ks.foldl (fun v k => v ^^^ a.m k) (a.g .eax) ∧ Keeps [.eax] a a' ∧
      a'.m = a.m := by
  induction ks generalizing a with
  | nil => exact ⟨a, rfl, rfl, fun _ _ => rfl, rfl⟩
  | cons k ks ih =>
    rw [List.map_cons]
    refine WA.append (l₁ := [_]) ?_
    simp only [WA, xorM, evalA, stepA, srcA, slotOf_slot (hk k (List.mem_cons_self ..)), reduceCtorEq, or_self, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    obtain ⟨b, e, h1, h2, h3⟩ := ih (fun k h => hk k (List.mem_cons_of_mem _ h)) (a.set .eax (a.g .eax ^^^ a.m k))
    exact ⟨b, e, h1, fun r hr => (h2 r hr).trans (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp only [A.g_set, hr, ite_false]), h3⟩

theorem sumWords_ok (k : Nat) (ks : List Nat) (h : ∀ j ∈ k :: ks, j < 64) (a : A) :
    WA (sumWords (k :: ks)) a fun a' => a'.g .eax = sumOf a.m (k :: ks) ∧ Keeps [.eax] a a' ∧ a'.m = a.m := by
  rw [sumWords]
  refine WA.append (l₁ := [_]) ?_
  simp only [WA, ld, evalA, stepA, srcA, slotOf_slot (h k (List.mem_cons_self ..)), reduceCtorEq, or_self, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  obtain ⟨b, e, h1, h2, h3⟩ := xors_ok ks (fun j hj => h j (List.mem_cons_of_mem _ hj)) (a.set .eax (a.m k))
  exact ⟨b, e, h1, fun r hr => (h2 r hr).trans (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp only [A.g_set, hr, ite_false]), h3⟩

/-! ### The product -/

abbrev work : List Reg := [.eax, .edx, .ebx, .esi, .edi, .ebp]

theorem take_ok (a : A) :
    WA [xorR .edi .ebx, xorR .ebp .esi] a fun a' =>
      a'.g .ebp ++ a'.g .edi = (a.g .ebp ++ a.g .edi) ^^^ (a.g .esi ++ a.g .ebx) ∧ Keeps [.edi, .ebp] a a' ∧ a'.m = a.m := by
  simp only [WA, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, trivial⟩
  · exact Spread.xor_append' .. |>.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem append_split {v : BitVec 64} {b c : BitVec 32} (h : b ++ c = v) : c = v.extractLsb' 0 32 ∧ b = v.extractLsb' 32 32 := by
  subst h
  refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> rw [BitVec.extractLsb'_toNat, toNat_append] <;>
    have := b.isLt <;> have := c.isLt <;> omega

theorem mul32_ok (k : Nat) (ks : List Nat) (t : Nat) (hks : ∀ j ∈ k :: ks, j < 64) (ht : t < 7) (kw : BitVec 32) (a : A)
    (hK : Cls a (4 * t) kw) :
    WA (mul32 (k :: ks) t) a fun a' =>
      a'.g .edi = (mul32x (sumOf a.m (k :: ks)) kw).1 ∧ a'.g .ebp = (mul32x (sumOf a.m (k :: ks)) kw).2 ∧
      Keeps work a a' ∧ ∀ j, j < 28 ∨ 32 ≤ j → a'.m j = a.m j := by
  generalize hw : sumOf a.m (k :: ks) = w
  rw [mul32]
  simp only [List.append_assoc]
  refine WA.append ((sumWords_ok k ks hks a).mono fun b ⟨e₁, g₁, m₁⟩ => ?_)
  refine WA.append ((split_ok 28 .eax (by decide) (by decide) b).mono fun c ⟨C, m₂, g₂⟩ => ?_)
  rw [e₁, hw] at C
  have hKc : Cls c (4 * t) kw := fun j hj => by rw [m₂ _ (by omega), m₁, hK j hj]
  have Mc : ∀ j, j < 28 ∨ 32 ≤ j → c.m j = a.m j := fun j hj => by rw [m₂ j hj, m₁]
  have kc : Keeps work a c := (g₁.mono (by decide)).trans (g₂.mono (by decide))
  have hC : ∀ r < 4, ∀ d : A, d.m = c.m → WA (classSum t r) d fun d' =>
      d'.g .esi ++ d'.g .ebx = meet4 (w.setWidth 64) (kw.setWidth 64) r &&& m4 r ∧ Keeps cw d d' ∧ d'.m = c.m :=
    fun r hr d hd => (classSum_ok t r ht hr w kw d (by rw [Cls, hd]; exact C) (by rw [Cls, hd]; exact hKc)).mono
      fun d' ⟨e, g, m⟩ => ⟨e, g, m.trans hd⟩
  refine WA.append ((hC 0 (by decide) c rfl).mono fun d ⟨e₃, g₃, m₃⟩ => ?_)
  refine WA.append (WA.mono (Q := fun e => e.g .ebp ++ e.g .edi = d.g .esi ++ d.g .ebx ∧ Keeps [.edi, .ebp] d e ∧ e.m = d.m)
    ?_ fun e ⟨e₄, g₄, m₄⟩ => ?_)
  · simp only [WA, mv, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
      reduceCtorEq, or_self, ite_false, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((hC 1 (by decide) e (m₄.trans m₃)).mono fun f ⟨e₅, g₅, m₅⟩ => ?_)
  refine WA.append ((take_ok f).mono fun g ⟨e₆, g₆, m₆⟩ => ?_)
  refine WA.append ((hC 2 (by decide) g (m₆.trans m₅)).mono fun h ⟨e₇, g₇, m₇⟩ => ?_)
  refine WA.append ((take_ok h).mono fun i ⟨e₈, g₈, m₈⟩ => ?_)
  refine WA.append ((hC 3 (by decide) i (m₈.trans m₇)).mono fun l ⟨e₉, g₉, m₉⟩ => ?_)
  refine (take_ok l).mono fun n ⟨e₁₀, g₁₀, m₁₀⟩ => ?_
  have hv : n.g .ebp ++ n.g .edi = mul4 (w.setWidth 64) (kw.setWidth 64) := by
    rw [e₁₀, g₉ _ (by decide), g₉ .edi (by decide), e₈, g₇ _ (by decide), g₇ .edi (by decide), e₆, g₅ _ (by decide),
      g₅ .edi (by decide), e₄, e₃, e₅, e₇, e₉, mul4]
  obtain ⟨v1, v2⟩ := append_split hv
  refine ⟨v1, v2, ?_, fun j hj => ?_⟩
  · exact kc.trans <| (g₃.mono (by decide)).trans <| (g₄.mono (by decide)).trans <| (g₅.mono (by decide)).trans <|
      (g₆.mono (by decide)).trans <| (g₇.mono (by decide)).trans <| (g₈.mono (by decide)).trans <|
      (g₉.mono (by decide)).trans <| g₁₀.mono (by decide)
  · rw [m₁₀, m₉, Mc j hj]

/-! ## The key -/

theorem ror_eq (z : BitVec 32) {k : Nat} (h0 : 0 < k) (hk : k < 32) : z.rotateRight k = z >>> k ^^^ z <<< (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h : i < 32 - k
  · simp [h]
  · simp [h, hi, BitVec.getLsbD_of_ge z (k + i) (by omega)]

theorem ror_ror (z : BitVec 32) {k l : Nat} (hk : k < 32) (hl : l < 32) (h : k + l < 32) :
    (z.rotateRight k).rotateRight l = z.rotateRight (k + l) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt h]
  by_cases h1 : i < 32 - l
  · simp only [h1, ite_true]
    by_cases h2 : l + i < 32 - k
    · simp only [h2, ite_true, show i < 32 - (k + l) by omega, Nat.add_assoc]
    · simp only [h2, ite_false, show ¬ i < 32 - (k + l) by omega, hi, show l + i < 32 by omega,
        show l + i - (32 - k) = i - (32 - (k + l)) by omega]
  · simp only [h1, ite_false, show ¬ i < 32 - (k + l) by omega, hi, show i - (32 - l) < 32 - k by omega, ite_true,
      decide_true, Bool.true_and, show k + (i - (32 - l)) = i - (32 - (k + l)) by omega]

/-- The key's words, of which `h₃` is `H`'s first. -/
def kws (h3 h2 h1 h0 : BitVec 32) : W4 :=
  ⟨h0 <<< 1 ^^^ h3 >>> 31, h1 <<< 1 ^^^ h0 >>> 31, h2 <<< 1 ^^^ h1 >>> 31, h3 <<< 1 ^^^ h2 >>> 31 ^^^ dn32 (h3 >>> 31)⟩

theorem add_self (v : BitVec 32) : v + v = v <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- A rotation of one bit. -/
theorem ror_bit (v : BitVec 32) {k : Nat} (h0 : 0 < k) (hk : k < 32) : (v >>> 31).rotateRight k = v >>> 31 <<< (32 - k) := by
  rw [ror_eq _ h0 hk, ← BitVec.shiftRight_add, BitVec.ushiftRight_eq_zero (by omega), BitVec.zero_xor]

theorem adjust_ok (a : A) :
    WA adjust a fun a' => (let k := kws (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi)
      a'.g .eax = k.w3 ∧ a'.g .ebx = k.w2 ∧ a'.g .esi = k.w1 ∧ a'.g .edi = k.w0) ∧ Keeps work a a' ∧ a'.m = a.m := by
  have r1 : ∀ v : BitVec 32, (v.rotateRight 1).rotateRight 1 = v.rotateRight 2 := fun v =>
    ror_ror v (by decide) (by decide) (by decide)
  have r2 : ∀ v : BitVec 32, (v.rotateRight 2).rotateRight 5 = v.rotateRight 7 := fun v =>
    ror_ror v (by decide) (by decide) (by decide)
  have b1 : ∀ v : BitVec 32, (v >>> 31).rotateRight 1 = v >>> 31 <<< 31 := fun v => ror_bit v (by decide) (by decide)
  have b2 : ∀ v : BitVec 32, (v >>> 31).rotateRight 2 = v >>> 31 <<< 30 := fun v => ror_bit v (by decide) (by decide)
  have b7 : ∀ v : BitVec 32, (v >>> 31).rotateRight 7 = v >>> 31 <<< 25 := fun v => ror_bit v (by decide) (by decide)
  simp only [WA, adjust, mv, shr, ror, xorR, evalA, stepA, srcA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    reduceCtorEq, or_self, Nat.reduceLeDiff, and_self, not_true_eq_false, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', r1, r2, add_self, kws, dn32]
  refine ⟨⟨?_, trivial⟩, fun r hr => ?_, trivial⟩
  · rw [b1, b2, b7]; simp only [BitVec.xor_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

/-! ## The vectors' code -/

theorem steps_ok (y k a m : XReg) (h1 : a ≠ y) (h2 : m ≠ y) (h3 : k ≠ y) (h4 : k ≠ a) (h5 : k ≠ m) (h6 : a ≠ m) (n : Nat)
    (b : A) :
    WA (steps y k a m n) b fun c => c.x y = (st128 (b.x k) n (b.x y)).1 ∧ c.x a = (st128 (b.x k) n (b.x y)).2 ∧
      VK [y, a, m] b c := by
  induction n with
  | zero =>
    simp only [WA, steps, vmv, vsh, vand, evalA, stepA, xopA, Option.bind_some, A.x_setX, h1.symm, h4,
      ite_false, ite_true, Option.some.injEq, exists_eq_left', eval_movdqa]
    refine ⟨by eqn, by eqn, by vk (VK.refl _ _)⟩
  | succ n ih =>
    rw [steps]
    refine WA.append (ih.mono fun c ⟨ey, ea, v⟩ => ?_)
    have ek : c.x k = b.x k := v.x k (by simp [h3, h4, h5])
    simp only [WA, step, vaddw, vmv, vsh, vand, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, h1,
      h1.symm, h2.symm, h3, h5, h6, h6.symm, ite_false, ite_true, Option.some.injEq, exists_eq_left', eval_movdqa, ey, ea, ek]
    refine ⟨by eqn, by eqn, by vk (v)⟩

abbrev v06 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6]

theorem vecs_code (j : Nat) (hj : 2 * j + 1 < 16) (b : A) (hc : b.x .xmm7 = c00ff) :
    WA (Impl.Gcm.X86.vecs j) b fun c =>
      c.x .xmm4 = (vecs (b.x .xmm0) (b.vec (2 * j)) (b.vec (2 * j + 1))).a ∧
      c.x .xmm3 = (vecs (b.x .xmm0) (b.vec (2 * j)) (b.vec (2 * j + 1))).b ∧ VK v06 b c := by
  rw [Impl.Gcm.X86.vecs]
  simp only [List.append_assoc]
  generalize hkl : b.vec (2 * j) = kl
  generalize hkh : b.vec (2 * j + 1) = kh
  generalize hw : b.x .xmm0 = w
  refine WA.append (WA.mono (Q := fun c => (c.x .xmm0 = w ∧ c.x .xmm1 = pxor (psllq w 8) w ∧ c.x .xmm4 = kh) ∧ VK v06 b c) ?_
    fun c ⟨⟨c0, c1, c4⟩, vc⟩ => ?_)
  · simp only [WA, vmv, vsh, vxor, vld, evalA, stepA, xopA, vslotOf_vslot hj, Option.map_some, Option.bind_some, A.x_setX,
      A.vec_setX, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left', eval_movdqa, hw, hkh]
    refine ⟨⟨by eqn, by eqn, by eqn⟩, by vk (VK.refl _ _)⟩
  refine WA.append ((steps_ok .xmm0 .xmm4 .xmm2 .xmm6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 7
    c).mono fun d ⟨d0, d2, vd⟩ => ?_)
  rw [c0, c4] at d0 d2
  have vd' : VK v06 b d := vc.trans (vd.mono (by decide))
  refine WA.append (WA.mono (Q := fun e => (e.x .xmm0 = paddw (st128 kh 7 w).1 (st128 kh 7 w).1 ∧ e.x .xmm5 = kl) ∧
    (e.x .xmm1 = pxor (psllq w 8) w ∧ e.x .xmm2 = (st128 kh 7 w).2 ∧ e.x .xmm4 = kh) ∧ VK v06 b e) ?_
    fun e ⟨⟨e0, e5⟩, ⟨e1, e2, e4⟩, ve⟩ => ?_)
  · have d1 : d.x .xmm1 = pxor (psllq w 8) w := (vd.x _ (by decide)).trans c1
    have d4 : d.x .xmm4 = kh := (vd.x _ (by decide)).trans c4
    have dk : d.vec (2 * j) = kl := (vd'.vec _).trans hkl
    simp only [WA, vaddw, vld, evalA, stepA, xopA, vslotOf_vslot (show 2 * j < 16 by omega), Option.map_some,
      Option.bind_some, A.x_setX, A.vec_setX, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left', d0, d1,
      d2, d4, dk]
    refine ⟨⟨by eqn, by eqn⟩, ⟨by eqn, by eqn, by eqn⟩, by vk (vd')⟩
  refine WA.append ((steps_ok .xmm0 .xmm5 .xmm3 .xmm6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 7
    e).mono fun f ⟨_, f3, vf⟩ => ?_)
  rw [e0, e5] at f3
  have vf' : VK v06 b f := ve.trans (vf.mono (by decide))
  refine WA.append (WA.mono (Q := fun g => (g.x .xmm4 = pxor kh kl ∧ g.x .xmm1 = pxor (psllq w 8) w ∧
    g.x .xmm2 = (st128 kh 7 w).2 ∧ g.x .xmm3 = f.x .xmm3) ∧ VK v06 b g) ?_ fun g ⟨⟨g4, g1, g2, g3⟩, vg⟩ => ?_)
  · have f4 : f.x .xmm4 = kh := (vf.x _ (by decide)).trans e4
    have f5 : f.x .xmm5 = kl := (vf.x _ (by decide)).trans e5
    have f1 : f.x .xmm1 = _ := (vf.x _ (by decide)).trans e1
    have f2 : f.x .xmm2 = _ := (vf.x _ (by decide)).trans e2
    simp only [WA, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true, Option.some.injEq,
      exists_eq_left', f4, f5, f1, f2]
    refine ⟨⟨by eqn, by eqn, by eqn, by eqn⟩, by vk (vf')⟩
  refine WA.append ((steps_ok .xmm1 .xmm4 .xmm5 .xmm6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 7
    g).mono fun h ⟨_, h5, vh⟩ => ?_)
  rw [g1, g4] at h5
  have vh' : VK v06 b h := vg.trans (vh.mono (by decide))
  have h2 : h.x .xmm2 = _ := (vh.x _ (by decide)).trans g2
  have h3 : h.x .xmm3 = _ := (vh.x _ (by decide)).trans (g3.trans f3)
  have h7 : h.x .xmm7 = c00ff := (vh'.x _ (by decide)).trans hc
  simp only [WA, vmv, vsh, vxor, vand, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
    Option.some.injEq, exists_eq_left', eval_movdqa, h2, h3, h5, h7]
  refine ⟨by eqn, by eqn, by vk (vh')⟩

theorem us_code (b : A) :
    WA us b fun c => (c.x .xmm1 = u1F (b.x .xmm0) ∧ c.x .xmm2 = u2F (b.x .xmm0) (u1F (b.x .xmm0))) ∧
      VK [.xmm1, .xmm2, .xmm3] b c := by
  simp only [WA, us, vmv, vsh, vxor, vor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
    Option.some.injEq, exists_eq_left', eval_movdqa]
  refine ⟨⟨by eqn, by eqn⟩, by vk (VK.refl _ _)⟩

theorem fix_code (q s : XReg) (hq : q ≠ .xmm6) (hs : s ≠ .xmm6) (b : A) :
    WA (Impl.Gcm.X86.fix q s) b fun c => c.x q = fix (b.x q) (b.x s) ∧ VK [q, .xmm6] b c := by
  simp only [WA, Impl.Gcm.X86.fix, vmv, vsh, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, hq, hs, ite_false,
    ite_true, Option.some.injEq, exists_eq_left', eval_movdqa]
  refine ⟨by eqn, by vk (VK.refl _ _)⟩

theorem vld_ok (d : XReg) (j : Nat) (hj : j < 16) (b : A) :
    WA [vld d j] b fun c => c.x d = b.vec j ∧ VK [d] b c := by
  simp only [WA, vld, evalA, stepA, vslotOf_vslot hj, Option.map_some, Option.bind_some, A.x_setX, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨by eqn, by vk (VK.refl _ _)⟩

theorem gather_code (b : A) :
    WA gather b fun c => (c.x .xmm0 = fix (b.vec 9) (b.x .xmm4) ∧ c.x .xmm1 = fix (b.vec 10) (b.x .xmm3) ∧
      c.x .xmm2 = fix (b.vec 11) (psrlq (b.x .xmm4) 32) ∧ c.x .xmm5 = fix (b.vec 15) (psrlq (b.x .xmm3) 32)) ∧
      VK v06 b c := by
  rw [gather]
  simp only [List.append_assoc]
  refine WA.append ((vld_ok .xmm0 9 (by decide) b).mono fun c ⟨c0, vc⟩ => ?_)
  refine WA.append ((fix_code .xmm0 .xmm4 (by decide) (by decide) c).mono fun d ⟨d0, vd⟩ => ?_)
  rw [c0, vc.x _ (by decide)] at d0
  refine WA.append ((vld_ok .xmm1 10 (by decide) d).mono fun e ⟨e1, ve⟩ => ?_)
  refine WA.append ((fix_code .xmm1 .xmm3 (by decide) (by decide) e).mono fun f ⟨f1, vf⟩ => ?_)
  rw [e1, ve.x _ (by decide), vd.x _ (by decide), vc.x _ (by decide), vd.vec, vc.vec] at f1
  have vf' : VK v06 b f := (vc.mono (by decide)).trans ((vd.mono (by decide)).trans ((ve.mono (by decide)).trans (vf.mono (by decide))))
  have f0 : f.x .xmm0 = _ := (vf.x _ (by decide)).trans ((ve.x _ (by decide)).trans d0)
  have f4 : f.x .xmm4 = b.x .xmm4 := by
    rw [vf.x _ (by decide), ve.x _ (by decide), vd.x _ (by decide), vc.x _ (by decide)]
  have f3 : f.x .xmm3 = b.x .xmm3 := by
    rw [vf.x _ (by decide), ve.x _ (by decide), vd.x _ (by decide), vc.x _ (by decide)]
  refine WA.append (WA.mono (Q := fun g => (g.x .xmm4 = psrlq (b.x .xmm4) 32 ∧ g.x .xmm3 = psrlq (b.x .xmm3) 32 ∧
    g.x .xmm2 = b.vec 11) ∧ VK [.xmm4, .xmm3, .xmm2] f g) ?_ fun g ⟨⟨g4, g3, g2⟩, vg⟩ => ?_)
  · have hk : f.vec 11 = b.vec 11 := vf'.vec 11
    simp only [WA, vsh, vld, zV, evalA, stepA, xopA, vslotOf_vslot (show 11 < 16 by decide), Option.map_some, Option.bind_some,
      A.x_setX, A.vec_setX, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left', f4, f3, hk]
    refine ⟨⟨by eqn, by eqn, by eqn⟩, by vk (VK.refl _ _)⟩
  refine WA.append ((fix_code .xmm2 .xmm4 (by decide) (by decide) g).mono fun h ⟨h2, vh⟩ => ?_)
  rw [g2, g4] at h2
  refine WA.append ((vld_ok .xmm5 15 (by decide) h).mono fun i ⟨i5, vi⟩ => ?_)
  refine (fix_code .xmm5 .xmm3 (by decide) (by decide) i).mono fun l ⟨l5, vl⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [vl.x _ (by decide), vi.x _ (by decide), vh.x _ (by decide), vg.x _ (by decide), f0]
  · rw [vl.x _ (by decide), vi.x _ (by decide), vh.x _ (by decide), vg.x _ (by decide), f1]
  · rw [vl.x _ (by decide), vi.x _ (by decide), h2]
  · rw [l5, i5, vi.x _ (by decide), vh.x _ (by decide), g3, vh.vec, vg.vec, vf'.vec]
  · exact vf'.trans ((vg.mono (by decide)).trans ((vh.mono (by decide)).trans ((vi.mono (by decide)).trans (vl.mono (by decide)))))

/-- The scalar product, in a vector. -/
def scalarV (lo hi : BitVec 32) : BitVec 128 := XBinOp.eval .punpckldq ((0 : BitVec 96) ++ lo) ((0 : BitVec 96) ++ hi)

theorem asm_code (b : A) :
    WA Impl.Gcm.X86.asm b fun c =>
      (let p := asm (b.x .xmm0) (b.x .xmm1) (b.x .xmm2) (b.x .xmm5) (scalarV (b.g .edi) (b.g .ebp))
       c.x .xmm0 = p.a ∧ c.x .xmm1 = p.b) ∧ VK v06 b c := by
  refine WA.append (l₁ := [.xop (.movd .xmm6 .edi), .xop (.movd .xmm3 .ebp), .xop (.bin .punpckldq .xmm6 .xmm3)]) ?_
  refine WA.mono (Q := fun c => c.x .xmm6 = scalarV (b.g .edi) (b.g .ebp) ∧ VK [.xmm6, .xmm3] b c) ?_ fun c ⟨c6, vc⟩ => ?_
  · refine ⟨_, by eqn, by eqn, by vk (VK.refl _ _)⟩
  have c0 := vc.x .xmm0 (by decide)
  have c1 := vc.x .xmm1 (by decide)
  have c2 := vc.x .xmm2 (by decide)
  have c5 := vc.x .xmm5 (by decide)
  generalize scalarV (b.g .edi) (b.g .ebp) = v at c6 ⊢
  generalize b.x .xmm0 = x at c0 ⊢
  generalize b.x .xmm1 = y at c1 ⊢
  generalize b.x .xmm2 = z at c2 ⊢
  generalize b.x .xmm5 = w at c5 ⊢
  refine WA.append (l₁ := [.xop (.pshufd .xmm3 .xmm0 0x4e), vxor .xmm3 .xmm0, .xop (.pshufd .xmm4 .xmm1 0x4e),
    vxor .xmm4 .xmm1, .xop (.bin .punpcklqdq .xmm3 .xmm4), vxor .xmm5 .xmm3]) ?_
  refine WA.mono (Q := fun d => (d.x .xmm5 = pxor w (lqdq (pxor (shufDwords x 0x4e) x) (pxor (shufDwords y 0x4e) y)) ∧
    d.x .xmm0 = x ∧ d.x .xmm1 = y ∧ d.x .xmm2 = z ∧ d.x .xmm6 = v) ∧ VK [.xmm3, .xmm4, .xmm5] c d) ?_
    fun d ⟨⟨d5, d0, d1, d2, d6⟩, vd⟩ => ?_
  · simp only [WA, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, exists_eq_left', c0, c1, c2, c5, c6]
    refine ⟨⟨by eqn, by eqn, by eqn, by eqn, by eqn⟩, by vk (VK.refl _ _)⟩
  simp only [asm]
  generalize pxor w (lqdq (pxor (shufDwords x 0x4e) x) (pxor (shufDwords y 0x4e) y)) = t at d5 ⊢
  simp only [WA, vmv, vsh, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
    Option.some.injEq, exists_eq_left', eval_movdqa, d0, d1, d2, d5, d6]
  refine ⟨⟨by eqn, by eqn⟩, by vk ((vc.mono (by decide)).trans (vd.mono (by decide)))⟩

theorem dn_code (b : A) : WA dn b fun c => c.x .xmm3 = dnV (b.x .xmm0) ∧ VK [.xmm3, .xmm4] b c := by
  simp only [WA, dn, vmv, vsh, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
    Option.some.injEq, exists_eq_left', eval_movdqa]
  refine ⟨by eqn, by vk (VK.refl _ _)⟩

theorem reduce_code (b : A) :
    WA reduce b fun c => c.x .xmm1 = redV ⟨b.x .xmm0, b.x .xmm1⟩ ∧ VK v06 b c := by
  rw [reduce]
  simp only [List.append_assoc]
  refine WA.append ((dn_code b).mono fun c ⟨c3, vc⟩ => ?_)
  refine WA.append (WA.mono (Q := fun d => d.x .xmm0 = pxor (b.x .xmm0) (pslldq (dnV (b.x .xmm0)) 8) ∧
    VK [.xmm0, .xmm3] c d) ?_ fun d ⟨d0, vd⟩ => ?_)
  · have c0 := vc.x .xmm0 (by decide)
    simp only [WA, vsh, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, exists_eq_left', c3, c0]
    refine ⟨by eqn, by vk (VK.refl _ _)⟩
  refine WA.append ((dn_code d).mono fun e ⟨e3, ve⟩ => ?_)
  rw [d0] at e3
  have e0 : e.x .xmm0 = _ := (ve.x _ (by decide)).trans d0
  have e1 : e.x .xmm1 = b.x .xmm1 := by rw [ve.x _ (by decide), vd.x _ (by decide), vc.x _ (by decide)]
  have ve' : VK v06 b e := (vc.mono (by decide)).trans ((vd.mono (by decide)).trans (ve.mono (by decide)))
  simp only [redV]
  generalize pxor (b.x .xmm0) (pslldq (dnV (b.x .xmm0)) 8) = r at e3 e0 ⊢
  simp only [WA, vmv, vsh, vxor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false, ite_true,
    Option.some.injEq, exists_eq_left', eval_movdqa, e3, e0, e1]
  refine ⟨by eqn, by vk (ve')⟩

/-- Stores of two vectors, then a load of one. -/
theorem vst2_ok (j i : Nat) (hj : j < 16) (hi : i < 16) (r q : XReg) (b : A) :
    WA [vst j r, vst i q] b fun c => c.x = b.x ∧ c.g = b.g ∧ (∀ k, c.vec k = if k = i then b.x q else if k = j then b.x r else b.vec k) ∧
      ∀ k, k / 4 ≠ j → k / 4 ≠ i → c.m k = b.m k := by
  simp only [WA, vst, evalA, stepA, vslotOf_vslot hj, vslotOf_vslot hi, Option.map_some, Option.bind_some, A.x_putV,
    Option.some.injEq, exists_eq_left', A.vec_putV, A.m_putV]
  exact ⟨by eqn, by eqn, fun k => by eqn, fun k h1 h2 => by rw [ite_eq_right h2, ite_eq_right h1]⟩

/-- Two stores of vectors, then a load of one. -/
theorem vst2ld_ok (j i l : Nat) (hj : j < 16) (hi : i < 16) (hl : l < 16) (r q d : XReg) (b : A) :
    WA [vst j r, vst i q, vld d l] b fun c => (c.x d = if l = i then b.x q else if l = j then b.x r else b.vec l) ∧
      (∀ x, x ≠ d → c.x x = b.x x) ∧ c.g = b.g ∧
      (∀ k, c.vec k = if k = i then b.x q else if k = j then b.x r else b.vec k) ∧
      ∀ k, k / 4 ≠ j → k / 4 ≠ i → c.m k = b.m k := by
  refine WA.append (l₁ := [vst j r, vst i q]) ((vst2_ok j i hj hi r q b).mono fun c ⟨cx, cg, cv, cm⟩ => ?_)
  refine (vld_ok d l hl c).mono fun e ⟨ed, v⟩ => ⟨by rw [ed, cv], fun x hx => ?_, v.g.trans cg, fun k => ?_, fun k h1 h2 => ?_⟩
  · rw [v.x x (by simpa using hx), cx]
  · rw [v.vec, cv]
  · rw [v.m, cm k h1 h2]

theorem vst_ok (j : Nat) (hj : j < 16) (r : XReg) (b : A) :
    WA [vst j r] b fun c => c.x = b.x ∧ c.g = b.g ∧ (∀ k, c.vec k = if k = j then b.x r else b.vec k) ∧
      ∀ k, k / 4 ≠ j → c.m k = b.m k := by
  refine ⟨b.putV j (b.x r), ?_, rfl, rfl, fun k => A.vec_putV .., fun k h => ite_eq_right h⟩
  simp only [vst, evalA, stepA, vslotOf_vslot hj, Option.map_some, Option.bind_some]

/-- The key's vectors. -/
structure KeyV (a : A) (K : BitVec 128) : Prop where
  l0 : a.vec 0 = kbl K
  h0 : a.vec 1 = kbh K
  l1 : a.vec 2 = kbl (u1F K)
  h1 : a.vec 3 = kbh (u1F K)
  l2 : a.vec 4 = kbl (u2F K (u1F K))
  h2 : a.vec 5 = kbh (u2F K (u1F K))

theorem KeyV.mem {a b : A} {K : BitVec 128} (h : KeyV a K) (hm : ∀ k < 24, b.m k = a.m k) : KeyV b K := by
  have e : ∀ j < 6, b.vec j = a.vec j := fun j hj => by
    rw [A.vec, A.vec, hm _ (by omega), hm _ (by omega), hm _ (by omega), hm _ (by omega)]
  exact ⟨(e 0 (by decide)).trans h.l0, (e 1 (by decide)).trans h.h0, (e 2 (by decide)).trans h.l1,
    (e 3 (by decide)).trans h.h1, (e 4 (by decide)).trans h.l2, (e 5 (by decide)).trans h.h2⟩

/-- The products of a block's lanes. -/
def prods : List Instr :=
  us ++ (([vst zV .xmm1, vst uV .xmm2] : List Instr) ++ (Impl.Gcm.X86.vecs 0 ++
    (([vst xV .xmm4, vst y'V .xmm3, vld .xmm0 zV] : List Instr) ++ (Impl.Gcm.X86.vecs 1 ++
    (([vst zV .xmm4, vst wV .xmm3, vld .xmm0 uV] : List Instr) ++ Impl.Gcm.X86.vecs 2)))))

theorem prods_ok {a : A} {K : BitVec 128} (hK : KeyV a K) (hc : a.x .xmm7 = c00ff) :
    WA prods a fun a' =>
      (let y := a.x .xmm0
       let p0 := vecs y (kbl K) (kbh K)
       let p1 := vecs (u1F y) (kbl (u1F K)) (kbh (u1F K))
       let p2 := vecs (u2F y (u1F y)) (kbl (u2F K (u1F K))) (kbh (u2F K (u1F K)))
       (a'.vec 9 = p0.a ∧ a'.vec 10 = p0.b ∧ a'.vec 11 = p1.a ∧ a'.vec 15 = p1.b) ∧
         a'.x .xmm4 = p2.a ∧ a'.x .xmm3 = p2.b) ∧
      a'.x .xmm7 = c00ff ∧ (∀ k, k < 32 ∨ 52 ≤ k ∧ k < 60 → a'.m k = a.m k) ∧ a'.g = a.g := by
  have keep : ∀ {b c : A} {i j : Nat}, 8 ≤ i → 8 ≤ j → (∀ k, k / 4 ≠ j → k / 4 ≠ i → c.m k = b.m k) →
      ∀ k < 24, c.m k = b.m k := fun hi hj h k hk => h k (by omega) (by omega)
  refine WA.append ((us_code a).mono fun b ⟨⟨b1, b2⟩, vb⟩ => ?_)
  refine WA.append ((vst2_ok 11 12 (by decide) (by decide) .xmm1 .xmm2 b).mono fun c ⟨cx, cg, cv, cm⟩ => ?_)
  rw [b1, b2] at cv
  have Kc : KeyV c K := hK.mem fun k hk => by rw [keep (by decide) (by decide) cm k hk, vb.m]
  have c0 : c.x .xmm0 = a.x .xmm0 := by rw [cx, vb.x _ (by decide)]
  have c7 : c.x .xmm7 = c00ff := by rw [cx, vb.x _ (by decide), hc]
  dsimp only
  generalize a.x .xmm0 = y at c0 cv ⊢
  refine WA.append ((vecs_code 0 (by decide) c c7).mono fun d ⟨d4, d3, vd⟩ => ?_)
  simp only [Nat.reduceMul, Nat.reduceAdd, c0, Kc.l0, Kc.h0] at d4 d3
  generalize vecs y (kbl K) (kbh K) = p0 at d4 d3 ⊢
  refine WA.append ((vst2ld_ok 9 10 11 (by decide) (by decide) (by decide) .xmm4 .xmm3 .xmm0 d).mono
    fun e ⟨e0, ex, eg, ev, em⟩ => ?_)
  rw [d4, d3] at ev
  simp only [Nat.reduceEqDiff, ite_false, vd.vec, cv, ite_true] at e0
  have e7 : e.x .xmm7 = c00ff := by rw [ex _ (by decide), vd.x _ (by decide), c7]
  have Ke : KeyV e K := Kc.mem fun k hk => by rw [keep (by decide) (by decide) em k hk, vd.m]
  refine WA.append ((vecs_code 1 (by decide) e e7).mono fun f ⟨f4, f3, vf⟩ => ?_)
  simp only [Nat.reduceMul, Nat.reduceAdd, e0, Ke.l1, Ke.h1] at f4 f3
  generalize vecs (u1F y) (kbl (u1F K)) (kbh (u1F K)) = p1 at f4 f3 ⊢
  refine WA.append ((vst2ld_ok 11 15 12 (by decide) (by decide) (by decide) .xmm4 .xmm3 .xmm0 f).mono
    fun g ⟨g0, gx, gg, gv, gm⟩ => ?_)
  rw [f4, f3] at gv
  simp only [Nat.reduceEqDiff, ite_false, vf.vec, ev, vd.vec, cv, ite_true] at g0
  have g7 : g.x .xmm7 = c00ff := by rw [gx _ (by decide), vf.x _ (by decide), e7]
  have Kg : KeyV g K := Ke.mem fun k hk => by rw [keep (by decide) (by decide) gm k hk, vf.m]
  refine (vecs_code 2 (by decide) g g7).mono fun h ⟨h4, h3, vh⟩ => ?_
  simp only [Nat.reduceMul, Nat.reduceAdd, g0, Kg.l2, Kg.h2] at h4 h3
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, h4, h3⟩, (vh.x _ (by decide)).trans g7, fun k hk => ?_, ?_⟩
  · simp only [vh.vec, gv, vf.vec, ev, Nat.reduceEqDiff, ite_false, ite_true]
  · simp only [vh.vec, gv, vf.vec, ev, Nat.reduceEqDiff, ite_false, ite_true]
  · simp only [vh.vec, gv, Nat.reduceEqDiff, ite_false, ite_true]
  · simp only [vh.vec, gv, Nat.reduceEqDiff, ite_false, ite_true]
  · rw [vh.m, gm k (by omega) (by omega), vf.m, em k (by omega) (by omega), vd.m, cm k (by omega) (by omega), vb.m]
  · rw [vh.g, gg, vf.g, eg, vd.g, cg, vb.g]

theorem vpart_ok {a : A} {K : BitVec 128} (hK : KeyV a K) (hc : a.x .xmm7 = c00ff) :
    WA vpart a fun a' =>
      a'.vec 8 = prodV (a.x .xmm0) (kbl K) (kbh K) (kbl (u1F K)) (kbh (u1F K)) (kbl (u2F K (u1F K)))
        (kbh (u2F K (u1F K))) (scalarV (a.g .edi) (a.g .ebp)) ∧
      a'.x .xmm7 = c00ff ∧ (∀ k, k < 32 ∨ 52 ≤ k ∧ k < 60 → a'.m k = a.m k) ∧ a'.g = a.g := by
  have hv : vpart = prods ++ (gather ++ (Impl.Gcm.X86.asm ++ (reduce ++ [vst yV .xmm1]))) := by
    simp only [vpart, prods, List.append_assoc]
  rw [hv]
  refine WA.append ((prods_ok hK hc).mono fun h ⟨⟨⟨v9, v10, v11, v15⟩, h4, h3⟩, h7, hm, hg⟩ => ?_)
  simp only [prodV]
  generalize vecs (a.x .xmm0) (kbl K) (kbh K) = p0 at v9 v10 ⊢
  generalize vecs (u1F (a.x .xmm0)) (kbl (u1F K)) (kbh (u1F K)) = p1 at v11 v15 ⊢
  generalize vecs (u2F (a.x .xmm0) (u1F (a.x .xmm0))) (kbl (u2F K (u1F K))) (kbh (u2F K (u1F K))) = p2 at h4 h3 ⊢
  refine WA.append ((gather_code h).mono fun i ⟨⟨i0, i1, i2, i5⟩, vi⟩ => ?_)
  rw [v9, h4] at i0
  rw [v10, h3] at i1
  rw [v11, h4] at i2
  rw [v15, h3] at i5
  refine WA.append ((asm_code i).mono fun l ⟨⟨l0, l1⟩, vl⟩ => ?_)
  rw [i0, i1, i2, i5, vi.g, hg] at l0 l1
  refine WA.append ((reduce_code l).mono fun n ⟨n1, vn⟩ => ?_)
  rw [l0, l1] at n1
  refine (vst_ok 8 (by decide) .xmm1 n).mono fun o ⟨ox, og, ov, om⟩ => ⟨?_, ?_, fun k hk => ?_, ?_⟩
  · rw [ov, ite_eq_left rfl, n1]
  · rw [ox, vn.x _ (by decide), vl.x _ (by decide), vi.x _ (by decide), h7]
  · rw [om k (by omega), vn.m, vl.m, vi.m, hm k hk]
  · rw [og, vn.g, vl.g, vi.g, hg]

/-! ## The key's vectors -/

theorem bytes_ok (r : XReg) (j : Nat) (hj : 2 * j + 1 < 16) (hr : r ≠ .xmm3) (a : A) (hc : a.x .xmm7 = c00ff) :
    WA (bytes r j) a fun a' =>
      (∀ k, a'.vec k = if k = 2 * j + 1 then kbh (a.x r) else if k = 2 * j then kbl (a.x r) else a.vec k) ∧
      (∀ q, q ≠ r → q ≠ .xmm3 → a'.x q = a.x q) ∧ (∀ k, k / 4 ≠ 2 * j → k / 4 ≠ 2 * j + 1 → a'.m k = a.m k) ∧ a'.g = a.g := by
  refine WA.append (l₁ := [vmv .xmm3 r, vand .xmm3 .xmm7, vxor r .xmm3, vsh .psrlq r 8])
    (WA.mono (Q := fun c => (c.x .xmm3 = kbl (a.x r) ∧ c.x r = kbh (a.x r)) ∧ VK [r, .xmm3] a c) ?_
      fun c ⟨⟨c3, cr⟩, vc⟩ => ?_)
  · simp only [WA, vmv, vsh, vxor, vand, evalA, stepA, xopA, Option.bind_some, A.x_setX, hr, hr.symm, reduceCtorEq, ite_false,
      ite_true, Option.some.injEq, exists_eq_left', eval_movdqa, hc]
    refine ⟨⟨by eqn, by eqn⟩, by vk (VK.refl _ _)⟩
  refine (vst2_ok (2 * j) (2 * j + 1) (by omega) hj .xmm3 r c).mono fun d ⟨dx, dg, dv, dm⟩ =>
    ⟨fun k => ?_, fun q h1 h2 => ?_, fun k h1 h2 => ?_, ?_⟩
  · rw [dv, c3, cr, vc.vec]
  · rw [dx, vc.x q (by simp [h1, h2])]
  · rw [dm k h1 h2, vc.m]
  · rw [dg, vc.g]

theorem setC_ok (a : A) : WA setC a fun a' => a'.x .xmm7 = c00ff ∧ a'.m = a.m ∧ Keeps [.eax] a a' := by
  refine ⟨_, rfl, ?_, rfl, fun r hr => ?_⟩
  · simp only [A.x_setX, A.g_set, ite_true]
    decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_setX, A.g_set, hr, ite_false]

theorem keyVecs_ok (a : A) (hc : a.x .xmm7 = c00ff) :
    WA keyVecs a fun a' => KeyV a' (a.vec 8) ∧ a'.x .xmm7 = c00ff ∧ (∀ k, 24 ≤ k → a'.m k = a.m k) ∧ a'.g = a.g := by
  rw [keyVecs]
  simp only [List.append_assoc]
  refine WA.append ((vld_ok .xmm0 8 (by decide) a).mono fun b ⟨b0, vb⟩ => ?_)
  generalize a.vec 8 = K at b0 ⊢
  refine WA.append ((us_code b).mono fun c ⟨⟨c1, c2⟩, vc⟩ => ?_)
  rw [b0] at c1 c2
  have c0 : c.x .xmm0 = K := (vc.x _ (by decide)).trans b0
  have c7 : c.x .xmm7 = c00ff := by rw [vc.x _ (by decide), vb.x _ (by decide), hc]
  refine WA.append ((bytes_ok .xmm0 0 (by decide) (by decide) c c7).mono fun d ⟨dv, dx, dm, dg⟩ => ?_)
  rw [c0] at dv
  refine WA.append ((bytes_ok .xmm1 1 (by decide) (by decide) d ((dx _ (by decide) (by decide)).trans c7)).mono
    fun e ⟨ev, ex, em, eg⟩ => ?_)
  rw [dx _ (by decide) (by decide), c1] at ev
  refine (bytes_ok .xmm2 2 (by decide) (by decide) e (by rw [ex _ (by decide) (by decide), dx _ (by decide) (by decide), c7])).mono
    fun f ⟨fv, fx, fm, fg⟩ => ⟨?_, ?_, fun k hk => ?_, ?_⟩
  · rw [ex _ (by decide) (by decide), dx _ (by decide) (by decide), c2] at fv
    constructor <;> simp [fv, ev, dv]
  · rw [fx _ (by decide) (by decide), ex _ (by decide) (by decide), dx _ (by decide) (by decide), c7]
  · rw [fm k (by omega) (by omega), em k (by omega) (by omega), dm k (by omega) (by omega), vc.m, vb.m]
  · rw [fg, eg, dg, vc.g, vb.g]

/-- The sum of a vector's doublewords. -/
def xsum (v : BitVec 128) : BitVec 32 := sumOf (dword v) [0, 1, 2, 3]

theorem sum_y (a : A) : sumOf a.m [32, 33, 34, 35] = xsum (a.vec 8) := by
  simp only [xsum, sumOf, List.foldl, A.vec, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem storeYs_ok (a : A) :
    WA storeYs a fun a' => a'.vec 8 = ofDwords (a.g .edi) (a.g .esi) (a.g .ebx) (a.g .eax) ∧
      (∀ k, k < 32 ∨ 36 ≤ k → a'.m k = a.m k) ∧ a'.g = a.g := by
  simp only [Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte, WA, storeYs, st, yS, evalA, stepA,
    slotOf_slot, Option.map_some, Option.bind_some, A.vec, A.g_put, A.m_put, Option.some.injEq, exists_eq_left']
  refine ⟨by eqn, fun k hk => ?_, by eqn⟩
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- What the key's words of `scratch` hold, and the constant's register. -/
structure KeysV (a : A) (K : BitVec 128) : Prop where
  v : KeyV a K
  s : Cls a 24 (xsum K)
  c : a.x .xmm7 = c00ff

theorem KeysV.mem {a b : A} {K : BitVec 128} (h : KeysV a K) (hm : ∀ k < 28, b.m k = a.m k) (hx : b.x .xmm7 = a.x .xmm7) :
    KeysV b K :=
  ⟨h.v.mem fun k hk => hm k (by omega), fun j hj => by rw [hm _ (by omega), h.s j hj], hx.trans h.c⟩

theorem keyCode_ok (a : A) :
    WA keyCode a fun a' => (let k := kws (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi)
      KeysV a' (ofDwords k.w0 k.w1 k.w2 k.w3)) ∧ (∀ j, 52 ≤ j → a'.m j = a.m j) ∧ Keeps work a a' := by
  rw [keyCode]
  simp only [List.append_assoc]
  refine WA.append ((adjust_ok a).mono fun b ⟨⟨e3, e2, e1, e0⟩, gb, mb⟩ => ?_)
  generalize hk : kws (a.g .eax) (a.g .ebx) (a.g .esi) (a.g .edi) = k at e3 e2 e1 e0 ⊢
  refine WA.append ((storeYs_ok b).mono fun c ⟨yc, mc, gc⟩ => ?_)
  rw [e3, e2, e1, e0] at yc
  generalize ofDwords k.w0 k.w1 k.w2 k.w3 = K at yc ⊢
  refine WA.append ((sumWords_ok 32 [33, 34, 35] (by decide) c).mono fun d ⟨ed, gd, md⟩ => ?_)
  rw [sum_y, yc] at ed
  refine WA.append ((split_ok 24 .eax (by decide) (by decide) d).mono fun e ⟨ce, me, ge⟩ => ?_)
  rw [ed] at ce
  refine WA.append ((setC_ok e).mono fun f ⟨f7, mf, gf⟩ => ?_)
  refine (keyVecs_ok f f7).mono fun g ⟨vg, g7, mg, gg⟩ => ⟨⟨?_, fun j hj => ?_, g7⟩, fun j hj => ?_, fun r hr => ?_⟩
  · have : f.vec 8 = K := by
      rw [← yc, A.vec, A.vec, mf, me _ (by decide), me _ (by decide), me _ (by decide), me _ (by decide), md]
    rwa [this] at vg
  · rw [mg _ (by omega), mf, ce j hj]
  · rw [mg _ (by omega), mf, me _ (by omega), md, mc _ (by omega), mb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [gg, gf r (by simp [hr]), ge r (by simp [hr]), gd r (by simp [hr]), gc, gb r (by simp [hr])]

/-! ## A block -/

theorem qword_scalarV (lo hi : BitVec 32) :
    lp (qword (scalarV lo hi) 0) = lp lo + X ^ 32 * lp hi := by
  have e : ∀ v : BitVec 32, dword ((0 : BitVec 96) ++ v : BitVec 128) 0 = v := fun v => by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_dword, BitVec.getLsbD_append]
    simp [hi]
  rw [lp_qword, scalarV, punpckldq_eq, e, e, dword_ofDwords_0, dword_ofDwords_1]

theorem lp_xsum (v : BitVec 128) : lp (xsum v) = lp (dword v 0) + lp (dword v 2) + lp (dword v 1) + lp (dword v 3) := by
  show lp (dword v 0 ^^^ dword v 1 ^^^ dword v 2 ^^^ dword v 3) = _
  rw [lp_xor, lp_xor, lp_xor, add_right_comm (lp (dword v 0))]

theorem revx_ok (a : A) (hc : a.x .xmm7 = c00ff) :
    WA rev a fun a' => a'.x .xmm0 = revV (a.x .xmm0) ∧ VK [.xmm0, .xmm1] a a' := by
  simp only [WA, rev, vmv, vsh, vxor, vand, vor, evalA, stepA, xopA, Option.bind_some, A.x_setX, reduceCtorEq, ite_false,
    ite_true, Option.some.injEq, exists_eq_left', eval_movdqa, hc]
  refine ⟨by eqn, by vk (VK.refl _ _)⟩

theorem addX_ok (a : A) (hc : a.x .xmm7 = c00ff) :
    WA addX a fun a' => a'.x .xmm0 = pxor (revV (a.x .xmm0)) (a.vec 8) ∧ a'.vec 8 = pxor (revV (a.x .xmm0)) (a.vec 8) ∧
      a'.x .xmm7 = c00ff ∧ (∀ k, k < 32 ∨ 36 ≤ k → a'.m k = a.m k) ∧ a'.g = a.g := by
  refine WA.append ((revx_ok a hc).mono fun b ⟨b0, vb⟩ => ?_)
  refine WA.append (l₁ := [vld .xmm1 yV, vxor .xmm0 .xmm1]) (WA.mono
    (Q := fun c => c.x .xmm0 = pxor (revV (a.x .xmm0)) (a.vec 8) ∧ VK [.xmm0, .xmm1] b c) ?_ fun c ⟨c0, vc⟩ => ?_)
  · have e : b.vec 8 = a.vec 8 := vb.vec 8
    simp only [WA, vld, vxor, yV, evalA, stepA, xopA, vslotOf_vslot (show 8 < 16 by decide), Option.map_some, Option.bind_some,
      A.x_setX, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left', b0, e]
    refine ⟨by eqn, by vk (VK.refl _ _)⟩
  refine (vst_ok 8 (by decide) .xmm0 c).mono fun d ⟨dx, dg, dv, dm⟩ => ⟨?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [dx, c0]
  · rw [dv, ite_eq_left rfl, c0]
  · rw [dx, vc.x _ (by decide), vb.x _ (by decide), hc]
  · rw [dm k (by omega), vc.m, vb.m]
  · rw [dg, vc.g, vb.g]

/-- A block's arithmetic, its bytes in `xmm0`. -/
def core : List Instr := addX ++ (mul32 yWords allT ++ vpart)

theorem core_ok {a : A} {K : BitVec 128} {h1 h0 : BitVec 64} (hK : KeysV a K) (hk : K = keyW1 h1 h0 ++ keyW0 h1 h0) :
    WA core a fun a' =>
      a'.vec 8 = Spec.Gcm.mul (revV (a.x .xmm0) ^^^ a.vec 8) (h1 ++ h0 : BitVec 128) ∧
      (∀ k, k < 28 ∨ 52 ≤ k ∧ k < 60 → a'.m k = a.m k) ∧ a'.x .xmm7 = a.x .xmm7 ∧ Keeps work a a' := by
  refine WA.append ((addX_ok a hK.c).mono fun b ⟨b0, bv, b7, bm, bg⟩ => ?_)
  rw [show pxor (revV (a.x .xmm0)) (a.vec 8) = revV (a.x .xmm0) ^^^ a.vec 8 from rfl] at b0 bv
  generalize revV (a.x .xmm0) ^^^ a.vec 8 = y at b0 bv ⊢
  have Kb : KeysV b K := hK.mem (fun k hk => bm k (.inl (by omega))) (b7.trans hK.c.symm)
  refine WA.append (((mul32_ok 32 [33, 34, 35] allT (by decide) (by decide) (xsum K) b Kb.s).x (by decide)).mono
    fun c ⟨⟨e0, e1, gc, mc⟩, xc⟩ => ?_)
  rw [sum_y, bv] at e0 e1
  have Kc : KeysV c K := Kb.mem (fun k hk => mc k (.inl hk)) (by rw [xc])
  refine (vpart_ok Kc.v Kc.c).mono fun d ⟨dv, d7, dm, dg⟩ => ⟨?_, fun k hk => ?_, d7.trans hK.c.symm, ?_⟩
  · rw [dv, xc, b0, e0, e1, ← append_qword y]
    refine prodV_ok rfl hk ?_
    rw [qword_scalarV, Spread.isMul_mul32x, lp_xsum, lp_xsum, append_qword]
  · rw [dm k (by omega), mc k (by omega), bm k (by omega)]
  · exact fun r hr => by rw [dg, gc r hr, bg]

/-! ## The whole function -/

section
variable (s₀ : State)

abbrev hA : Addr := (hP s₀).setWidth 64
abbrev yA : Addr := (yP s₀).setWidth 64
abbrev dA : Addr := (dP s₀).setWidth 64
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yA s₀)

/-- The address of block `i`, in 32 bits. -/
abbrev blk (i : Nat) : BitVec 32 := dP s₀ + BitVec.ofNat 32 (16 * i)

/-- The words of a block. -/
abbrev wd (p : Addr) (o : Nat) : BitVec 32 := bswap (s₀.mem.readW (p + BitVec.ofNat 64 o) 32)

end

/-- The block of four words. -/
abbrev w4 (a b c d : BitVec 32) : BitVec 128 := a ++ b ++ c ++ d

theorem w4_eq (a b c d : BitVec 32) : w4 a b c d = ((a ++ b : BitVec 64) ++ (c ++ d : BitVec 64) : BitVec 128) :=
  words4 a b c d

theorem wd_mem (m : Mem) (p : Addr) :
    w4 (bswap (m.readW (p + BitVec.ofNat 64 0) 32)) (bswap (m.readW (p + BitVec.ofNat 64 4) 32))
      (bswap (m.readW (p + BitVec.ofNat 64 8) 32)) (bswap (m.readW (p + BitVec.ofNat 64 12) 32)) = blockAt m p := by
  have h : Spec.Aes.bytesAt m p 16 =
      [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2), m (p + BitVec.ofNat 64 3),
        m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5), m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7),
        m (p + BitVec.ofNat 64 8), m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
        m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
        m (p + BitVec.ofNat 64 15)] := rfl
  have e : ∀ j : Nat, p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) := fun j => Offset.add_add p j 1
  simp only [bswap_readW, e, Nat.reduceAdd]
  rw [blockAt, h, ofBytes_16, w4_eq, bytes8, bytes8]

theorem wd_block (s₀ : State) (p : Addr) : w4 (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12) = blockAt s₀.mem p :=
  wd_mem s₀.mem p

theorem w4_xor (a b c d e f g h : BitVec 32) :
    w4 (a ^^^ e) (b ^^^ f) (c ^^^ g) (d ^^^ h) = w4 a b c d ^^^ w4 e f g h := by
  rw [w4_eq, w4_eq, w4_eq, ← Spread.xor_append', ← Spread.xor_append']
  exact BitVec.xor_append.symm

namespace GPre
variable {s₀ : State} (h : GPre s₀)
include h

theorem toScr : Scr s₀ := ⟨by rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), h.fS⟩
theorem mem_h : hR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_self ..
theorem mem_d : dR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mem_a : aR s₀ ∈ s₀.rd ++ s₀.wr := by
  rw [h.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem mem_y : yR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)

theorem arg_in {i : Nat} (hi : i < 5) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have hs := h.fSp
  have e : ∀ k < 5, argAddr s₀ k = (s₀.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * k) := fun k hk =>
    addr_eq (x := s₀.gpr .esp) (k := 4 + 4 * k) (by omega)
  rw [e i hi, ← Offset.add_add _ 4 (4 * i)]
  show Region.Contains ⟨argAddr s₀ 0, 20⟩ _ _
  rw [e 0 (by decide)]
  exact Offset.contains_base _ (by omega) (by omega)

end GPre

/-- A load from a region disjoint from `scratch`. -/
theorem ext_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {d : Reg} (hd : ¬ (d = .ecx ∨ d = .esp)) (op : MemOp) {R : Region}
    {p : Addr} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (sR s₀)) (hp : s.ea op = p) (hc : R.Contains p 4)
    {is : List Instr} {Q : State → Prop}
    (hq : ∀ s', Rel s₀ s' (a.set d (s₀.mem.readW p 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem op) :: is)) s Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, hq _ (h.set hd _)⟩
  show (readSrc s (.mem op)).map _ = _
  rw [readSrc, State.load32, hp, ite_eq_left ⟨R, by rw [h.rd, h.wr]; exact hR, hc⟩,
    h.m.frame.readW hc (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)]
  rfl

/-- A load of an argument. -/
theorem arg_ok {s₀ s : State} {a : A} (hp : GPre s₀) (h : Rel s₀ s a) (i : Nat) (hi : i < 5) :
    WP isa (.block [.mov .edx (.mem (argOp i))]) s fun s' => Rel s₀ s' (a.set .edx (arg s₀ i)) :=
  ext_ok h (by decide) (argOp i) hp.mem_a hp.aS (p := argAddr s₀ i)
    (by rw [State.ea, argOp, at_, h.g, h.esp]; rfl) (hp.arg_in hi) fun _ r => WP.block_nil r

/-- The four words of a block, as loaded. -/
structure Blk (s₀ : State) (p : Addr) (a a' : A) : Prop where
  w3 : bswap (a'.g .eax) = wd s₀ p 0
  w2 : bswap (a'.g .ebx) = wd s₀ p 4
  w1 : bswap (a'.g .esi) = wd s₀ p 8
  w0 : bswap (a'.g .edi) = wd s₀ p 12
  k : Keeps [.eax, .ebx, .esi, .edi] a a'
  m : a'.m = a.m
  x : a'.x = a.x

theorem loadBlk_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {R : Region}
    {p : BitVec 32} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (sR s₀)) (hp : a.g .edx = p) (hf : p.toNat + 16 ≤ 2 ^ 32)
    (hc : ∀ o ≤ 12, R.Contains (p.setWidth 64 + BitVec.ofNat 64 o) 4) :
    WP isa (.block loadBlk) s fun s' => ∃ a', Rel s₀ s' a' ∧ Blk s₀ (p.setWidth 64) a a' := by
  have he : ∀ {s' : State} {a' : A} (o : Nat), o ≤ 12 → Rel s₀ s' a' → a'.g .edx = p →
      s'.ea (at_ .edx o) = p.setWidth 64 + BitVec.ofNat 64 o := fun o ho h' hp' => by
    rw [State.ea, at_, h'.g, hp']; exact addr_eq (x := p) (k := o) (by omega)
  refine ext_ok h (by decide) (at_ .edx 0) hR hdis (he 0 (by decide) h hp) (hc 0 (by decide)) fun s₁ r₁ => ?_
  refine ext_ok r₁ (by decide) (at_ .edx 4) hR hdis (he 4 (by decide) r₁ hp) (hc 4 (by decide)) fun s₂ r₂ => ?_
  refine ext_ok r₂ (by decide) (at_ .edx 8) hR hdis (he 8 (by decide) r₂ hp) (hc 8 (by decide)) fun s₃ r₃ => ?_
  refine ext_ok r₃ (by decide) (at_ .edx 12) hR hdis (he 12 (by decide) r₃ hp) (hc 12 (by decide))
    fun s₄ r₄ => WP.block_nil ⟨_, r₄, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

/-! ### The invariant -/

/-- The key's vector. -/
abbrev kV (s₀ : State) (p : Addr) : BitVec 128 :=
  let k := kws (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12)
  ofDwords k.w0 k.w1 k.w2 k.w3

theorem kV_eq (s₀ : State) (p : Addr) :
    kV s₀ p = (keyW1 (wd s₀ p 0 ++ wd s₀ p 4) (wd s₀ p 8 ++ wd s₀ p 12) ++
      keyW0 (wd s₀ p 0 ++ wd s₀ p 4) (wd s₀ p 8 ++ wd s₀ p 12) : BitVec 128) := by
  rw [Spread.keyW1_append, Spread.keyW0_append]
  exact w4_eq ..

structure InvA (s₀ : State) (i : Nat) (a : A) : Prop where
  key : KeysV a (kV s₀ (hA s₀))
  sav : ∀ q ∈ saved, a.m q.2 = s₀.gpr q.1
  y : a.vec 8 = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dA s₀) i)
  dp : a.m dpS = blk s₀ i
  n : a.m nS = BitVec.ofNat 32 (nBlk s₀ - i)

def Inv (s₀ : State) (i : Nat) (s : State) : Prop := i ≤ nBlk s₀ ∧ ∃ a, Rel s₀ s a ∧ InvA s₀ i a

/-- A load of a block of the data. -/
theorem loadX_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {R : Region}
    {p : BitVec 32} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (sR s₀)) (hp : a.g .edx = p)
    (hc : R.Contains (p.setWidth 64) 16) :
    WP isa (.block loadX) s fun s' => Rel s₀ s' (a.setX .xmm0 (s₀.mem.readW (p.setWidth 64) 128)) := by
  have he : s.ea (at_ .edx 0) = p.setWidth 64 := by
    rw [State.ea, at_, h.g, hp]; exact congrArg _ (BitVec.add_zero _)
  refine WP.block_cons_iff.mpr ⟨_, ?_, WP.block_nil (h.setX .xmm0 _)⟩
  show (State.load128 _ _).map _ = _
  rw [State.load128, he, ite_eq_left ⟨R, by rw [h.rd, h.wr]; exact hR, hc⟩,
    h.m.frame.readW hc (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)]
  rfl

/-- A test of `eax`. -/
theorem test_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {k : Nat} (hk : k < 2 ^ 32) (hn : a.g .eax = BitVec.ofNat 32 k) :
    WP isa (.block test) s fun s' => Rel s₀ s' a ∧ s'.zf = some (decide (k = 0)) := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨h.flags .., ?_⟩⟩
  show some (s.gpr .eax &&& s.gpr .eax == 0) = _
  rw [BitVec.and_self, h.g, hn, Wp.ofNat_beq_zero hk]

theorem load_ok (d : Reg) (hd : ¬ (d = .ecx ∨ d = .esp)) (k : Nat) (hk : k < 64) (a : A) :
    WA [ld d k] a fun a' => a'.g d = a.m k ∧ Keeps [d] a a' ∧ a'.m = a.m := by
  simp only [WA, ld, evalA, stepA, srcA, hd, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_set, A.m_set, ite_false,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem advance_ok (a : A) :
    WA advance a fun a' => a'.m dpS = a.g .edx + 16 ∧
      (∀ k, k ≠ dpS → a'.m k = a.m k) ∧ Keeps [.edx] a a' := by
  simp only [WA, advance, st, dpS, evalA, stepA, srcA, slotOf_slot (show 56 < 64 by decide), reduceCtorEq, or_self, Option.map_some,
    Option.bind_some, A.g_set, A.m_set, A.m_put, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ite_eq_right hk, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem next_ok (a : A) :
    WA next a fun a' => a'.m nS = a.m nS + 0xffffffff ∧ a'.g .eax = a.m nS + 0xffffffff ∧
      (∀ k, k ≠ nS → a'.m k = a.m k) ∧ Keeps [.eax] a a' := by
  simp only [WA, next, ld, st, nS, evalA, stepA, srcA, slotOf_slot (show 57 < 64 by decide), reduceCtorEq, or_self,
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun k hk => ite_eq_right hk, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem ofNat_dec {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 32) : BitVec.ofNat 32 k + 0xffffffff = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (0xffffffff : BitVec 32).toNat = 2 ^ 32 - 1 from rfl]
  omega

theorem body_ok {s₀ : State} (hp : GPre s₀) {i : Nat} (hi : i < nBlk s₀) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  have hf := hp.fD
  have hn : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  obtain ⟨-, a, hr, ha⟩ := hI
  have hbody : body = [ld .edx dpS] ++ (loadX ++ (advance ++ (core ++ (next ++ test)))) := by
    simp only [body, core, List.append_assoc]
  have hba : (blk s₀ i).setWidth 64 = dA s₀ + BitVec.ofNat 64 (16 * i) := by
    have e : (blk s₀ i).toNat = (dP s₀).toNat + 16 * i := by
      rw [blk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact addr_eq (by omega)
  rw [hbody, WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr hr ((load_ok .edx (by decide) dpS (by decide) a).x (by decide)))
    fun s₁ ⟨a₁, r₁, ⟨e₁, k₁, m₁⟩, x₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadX_ok r₁ hp.mem_d hp.dDS (e₁.trans ha.dp) (by
    rw [hba]
    exact Offset.contains_base _ (by omega) (by omega))) fun s₂ r₂ => ?_
  rw [hba] at r₂
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₂ ((advance_ok _).x (by decide))) fun s₃ ⟨a₃, r₃, ⟨e₃, m₃, k₃⟩, x₃⟩ => ?_
  have m₃' : ∀ k, k ≠ dpS → a₃.m k = a.m k := fun k hk => by rw [m₃ k hk, A.m_setX, m₁]
  have x0 : a₃.x .xmm0 = s₀.mem.readW (dA s₀ + BitVec.ofNat 64 (16 * i)) 128 := by
    rw [x₃, A.x_setX, ite_eq_left rfl]
  have x7 : a₃.x .xmm7 = a.x .xmm7 := by rw [x₃, A.x_setX, ite_eq_right (by decide), x₁]
  have y₃ : a₃.vec 8 = a.vec 8 := by
    rw [A.vec, A.vec, m₃' _ (by decide), m₃' _ (by decide), m₃' _ (by decide), m₃' _ (by decide)]
  have key₃ : KeysV a₃ _ := ha.key.mem (fun k hk => m₃' k (by unfold dpS; omega)) x7
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₃ (core_ok key₃ (kV_eq s₀ (hA s₀)))) fun s₄ ⟨a₄, r₄, y₄, m₄, x₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₄ ((next_ok a₄).x (by decide))) fun s₅ ⟨a₅, r₅, ⟨n₅, n₅', m₅, k₅⟩, x₅⟩ => ?_
  have hcnt : a₄.m nS + 0xffffffff = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [m₄ nS (by decide), m₃' nS (by decide), ha.n]
    exact ofNat_dec (by omega) (by omega)
  refine WP.mono (test_ok r₅ (by omega) (n₅'.trans hcnt)) fun s₆ ⟨r₆, z₆⟩ => ⟨⟨hi, a₅, r₆, ?_⟩, z₆⟩
  refine ⟨ha.key.mem (fun k hk => ?_) (by rw [x₅, x₄, x7]), fun q hq => ?_, ?_, ?_, n₅.trans hcnt⟩
  · rw [m₅ k (by unfold nS; omega), m₄ k (.inl hk), m₃' k (by unfold dpS; omega)]
  · have hq' : ∀ q ∈ saved, (52 ≤ q.2 ∧ q.2 < 60) ∧ q.2 ≠ dpS ∧ q.2 ≠ nS := by decide
    obtain ⟨h1, h2, h3⟩ := hq' q hq
    rw [m₅ _ h3, m₄ _ (.inr h1), m₃' _ h2, ha.sav q hq]
  · have e : a₅.vec 8 = a₄.vec 8 := by
      rw [A.vec, A.vec, m₅ _ (by decide), m₅ _ (by decide), m₅ _ (by decide), m₅ _ (by decide)]
    rw [e, y₄, x0, revV_block, y₃, ghashFrom_blocksAt_succ, ← ha.y, BitVec.xor_comm, ← w4_eq, wd_block]
  · rw [m₅ dpS (by decide), m₄ dpS (by decide), e₃, A.g_setX, e₁, ha.dp, blk, blk, BitVec.add_assoc, Nat.mul_succ,
      BitVec.ofNat_add]
    rfl

/-! ### The prologue and the epilogue -/

theorem save_ok (a : A) : WA save a fun a' => (∀ q ∈ saved, a'.m q.2 = a.g q.1) ∧ a'.g = a.g := by
  simp only [Nat.reduceEqDiff, Nat.reduceLT, and_self, ↓reduceIte, WA, save, saved, st, List.map_cons, List.map_nil, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_self]

theorem st_ok (k : Nat) (hk : k < 64) (r : Reg) (a : A) :
    WA [st k r] a fun a' => a'.m k = a.g r ∧ (∀ j, j ≠ k → a'.m j = a.m j) ∧ a'.g = a.g := by
  simp only [WA, st, evalA, stepA, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_put, A.m_put,
    Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun j hj => ite_eq_right hj, trivial⟩

theorem rev_ok (a : A) :
    WA revBlk a fun a' => (a'.g .eax = bswap (a.g .eax) ∧ a'.g .ebx = bswap (a.g .ebx) ∧ a'.g .esi = bswap (a.g .esi) ∧
      a'.g .edi = bswap (a.g .edi)) ∧ Keeps [.eax, .ebx, .esi, .edi] a a' ∧ a'.m = a.m := by
  simp only [WA, revBlk, evalA, stepA, reduceCtorEq, or_self, Option.bind_some, A.g_set, A.m_set, ite_false, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_set, hr, ite_false]

theorem revKey_ok {s₀ : State} {a₁ a : A} {p : Addr} (B : Blk s₀ p a₁ a) :
    WA (revBlk ++ keyCode) a fun a' => KeysV a' (kV s₀ p) ∧ (∀ j, 52 ≤ j → a'.m j = a.m j) ∧ Keeps work a a' := by
  refine WA.append ((rev_ok a).mono fun b ⟨⟨e3, e2, e1, e0⟩, gb, mb⟩ => ?_)
  refine (keyCode_ok b).mono fun c ⟨K, mc, gc⟩ => ⟨?_, fun j hj => by rw [mc j hj, mb], (gb.mono (by decide)).trans gc⟩
  rwa [e3, e2, e1, e0, B.w3, B.w2, B.w1, B.w0] at K

theorem revY_ok {s₀ : State} {a₁ a : A} {p : Addr} (B : Blk s₀ p a₁ a) :
    WA (revBlk ++ (storeYs ++ [ld .eax nS])) a fun a' => a'.vec 8 = blockAt s₀.mem p ∧
      (∀ k, k < 32 ∨ 36 ≤ k → a'.m k = a.m k) ∧ a'.g .eax = a.m nS := by
  refine WA.append ((rev_ok a).mono fun b ⟨⟨e3, e2, e1, e0⟩, _, mb⟩ => ?_)
  refine WA.append ((storeYs_ok b).mono fun c ⟨y, mc, _⟩ => ?_)
  refine (load_ok .eax (by decide) nS (by decide) c).mono fun d ⟨e, _, md⟩ => ⟨?_, fun k hk => by rw [md, mc k hk, mb], ?_⟩
  · rw [← wd_block, A.vec, md]; refine Eq.trans y ?_
    rw [e3, e2, e1, e0, B.w3, B.w2, B.w1, B.w0]
    rfl
  · rw [e, mc _ (by decide), mb]

theorem prologue_ok {s₀ : State} (hp : GPre s₀) :
    WP isa (.block prologue) s₀ fun s' => Inv s₀ 0 s' ∧ s'.zf = some (decide (nBlk s₀ = 0)) := by
  have hpr : prologue = .mov .ecx (.mem (argOp 4)) :: (save ++ ([.mov .edx (.mem (argOp 2))] ++ ([st dpS .edx] ++
      ([.mov .edx (.mem (argOp 3))] ++ ([st nS .edx] ++ ([.mov .edx (.mem (argOp 0))] ++ (loadBlk ++ ((revBlk ++ keyCode) ++
      ([.mov .edx (.mem (argOp 1))] ++ (loadBlk ++ ((revBlk ++ (storeYs ++ [ld .eax nS])) ++ test))))))))))) := by
    simp only [prologue, List.append_assoc, List.cons_append, List.nil_append]
  have h0 : exec (.mov .ecx (.mem (argOp 4))) s₀ = some (s₀.setReg .ecx (sP s₀)) := by
    show (readSrc s₀ (.mem (argOp 4))).map _ = _
    rw [readSrc, State.load32, show s₀.ea (argOp 4) = argAddr s₀ 4 from rfl,
      ite_eq_left ⟨aR s₀, hp.mem_a, hp.arg_in (by decide)⟩]
    rfl
  have r₀ : Rel s₀ (s₀.setReg .ecx (sP s₀)) ⟨(s₀.setReg .ecx (sP s₀)).gpr,
      fun k => s₀.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32, s₀.xmm⟩ :=
    ⟨rfl, Slots32.init _ _ _, rfl, rfl, rfl, rfl, rfl⟩
  have gs : ∀ r, r ≠ .ecx → (s₀.setReg .ecx (sP s₀)).gpr r = s₀.gpr r := fun r hr => ite_eq_right hr
  rw [hpr]
  refine WP.block_cons_iff.mpr ⟨_, h0, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₀ (save_ok _)) fun s₁ ⟨a₁, r₁, hs, hg⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₁ 2 (by decide)) fun s₂ r₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₂ (st_ok dpS (by decide) .edx _)) fun s₃ ⟨a₃, r₃, d₃, m₃, g₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₃ 3 (by decide)) fun s₄ r₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₄ (st_ok nS (by decide) .edx _)) fun s₅ ⟨a₅, r₅, n₅, m₅, g₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₅ 0 (by decide)) fun s₆ r₆ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₆ hp.mem_h hp.dHS (p := hP s₀) rfl hp.fH
    (fun o ho => Offset.contains_base _ (by omega) (by omega))) fun s₇ ⟨a₇, r₇, B⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₇ (revKey_ok B)) fun s₈ ⟨a₈, r₈, K₈, m₈, g₈⟩ => ?_
  rw [B.m] at m₈
  rw [WP.block_append_iff]
  refine WP.mono (arg_ok hp r₈ 1 (by decide)) fun s₉ r₉ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₉ hp.mem_y hp.dYS (p := yP s₀) rfl hp.fY
    (fun o ho => Offset.contains_base _ (by omega) (by omega))) fun s₁₀ ⟨a₁₀, r₁₀, C⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₁₀ ((revY_ok C).x (by decide))) fun s₁₁ ⟨a₁₁, r₁₁, ⟨y₁₁, m₁₁, n₁₁⟩, x₁₁⟩ => ?_
  rw [C.m] at m₁₁ n₁₁
  have hm : ∀ k, 52 ≤ k → a₁₁.m k = a₅.m k := fun k hk => (m₁₁ k (.inr (by omega))).trans (m₈ k (by omega))
  have hn₅ : a₅.m nS = BitVec.ofNat 32 (nBlk s₀) := by
    rw [n₅, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine WP.mono (test_ok r₁₁ (arg s₀ 3).isLt (n₁₁.trans ((m₈ nS (by decide)).trans hn₅))) fun s₁₂ ⟨r₁₂, z₁₂⟩ =>
    ⟨⟨Nat.zero_le _, a₁₁, r₁₂, K₈.mem (fun k hk => m₁₁ k (.inl (by omega))) (by rw [x₁₁, C.x]; rfl), fun q hq => ?_, ?_, ?_,
      (hm _ (by decide)).trans hn₅⟩, z₁₂⟩
  · have hq' : ∀ q ∈ saved, 52 ≤ q.2 ∧ q.1 ≠ .ecx ∧ q.2 ≠ nS ∧ q.2 ≠ dpS := by decide
    obtain ⟨h1, h2, h3, h4⟩ := hq' q hq
    rw [hm _ h1, m₅ _ h3]
    refine (m₃ _ h4).trans ((hs q hq).trans (gs _ h2))
  · rw [ghashFrom_blocksAt_zero]; exact y₁₁
  · rw [hm _ (by decide), m₅ _ (by decide)]
    refine Eq.trans d₃ ?_
    rw [blk, Nat.mul_zero]; exact (BitVec.add_zero _).symm

theorem finish_ok (a : A) :
    WA finish a fun a' => (a'.m 32 = bswap (a.m 35) ∧ a'.m 33 = bswap (a.m 34) ∧ a'.m 34 = bswap (a.m 33) ∧
        a'.m 35 = bswap (a.m 32)) ∧ (∀ q ∈ saved, a'.g q.1 = a.m q.2) ∧ Keeps work a a' := by
  simp only [reduceCtorEq, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceAdd, or_self, and_self, ↓reduceIte, WA, finish, revBlk, restore, saved, ld, st, yS, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, evalA, stepA, srcA, slotOf_slot, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    A.g_put, A.m_put, Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_self, true_and]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem epilogue_ok {s₀ : State} (hp : GPre s₀) {s : State} (hI : Inv s₀ (nBlk s₀) s) :
    WP isa (.block epilogue) s fun s' => abiPreserved s₀ s' ∧ ghashX86.post s₀ s' := by
  obtain ⟨-, a, r, ha⟩ := hI
  have hfs := hp.fS
  have hfy := hp.fY
  have hfp := hp.fSp
  rw [epilogue, WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r (finish_ok a)) fun s₁ ⟨a₁, r₁, ⟨m0, m1, m2, m3⟩, hs, hk⟩ => ?_
  refine (WP.block_append_iff (l₁ := [_])).mpr ?_
  refine WP.mono (arg_ok hp r₁ 1 (by decide)) fun s₂ r₂ => ?_
  have hsc : s₂.ea (slot yS) = (sP s₀).setWidth 64 + BitVec.ofNat 64 128 := by
    rw [State.ea, slot, at_, r₂.g, r₂.ecx]; exact addr_eq (x := sP s₀) (k := 128) (by omega)
  have hl : exec (.movdquLoad .xmm0 (slot yS)) s₂ = some (s₂.setXmm .xmm0
      (s₂.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 128) 128)) := by
    show (State.load128 _ _).map _ = _
    rw [State.load128, hsc, ite_eq_left ⟨sR s₀, List.mem_append_right _ (by rw [r₂.wr]; exact hp.toScr.mem),
      Offset.contains_base _ (by decide) (by decide)⟩]
    rfl
  refine WP.block_cons_iff.mpr ⟨_, hl, ?_⟩
  generalize hv : s₂.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 128) 128 = v
  have hst : exec (.movdquStore (at_ .edx 0) .xmm0) (s₂.setXmm .xmm0 v) =
      some { s₂.setXmm .xmm0 v with mem := s₂.mem.writeW (yA s₀) v } := by
    show State.store128 _ _ _ = _
    have he : (s₂.setXmm .xmm0 v).ea (at_ .edx 0) = yA s₀ := by
      show (s₂.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
      rw [r₂.g]
      exact congrArg _ (BitVec.add_zero _)
    rw [State.store128, he, ite_eq_left ⟨yR s₀, by
      show _ ∈ s₂.wr; rw [r₂.wr, hp.wr]; exact List.mem_cons_self .., Region.contains_self _ _⟩]
    rfl
  refine WP.block_cons_iff.mpr ⟨_, hst, WP.block_nil ⟨⟨fun q hq => ?_, ?_⟩, ?_⟩⟩
  · have hsv : ∀ p ∈ saved, a₁.g p.1 = s₀.gpr p.1 := fun p hp => by rw [hs p hp, ha.sav p hp]
    have hq' : ∀ q ∈ calleeSaved, q ≠ .edx ∧ (q = .esp ∨ ∃ p ∈ saved, p.1 = q) := by decide
    show s₂.gpr q = _
    obtain ⟨hne, rfl | ⟨p, hp', rfl⟩⟩ := hq' q hq
    · rw [r₂.g, r₂.esp]
    · rw [r₂.g, A.g_set, ite_eq_right hne, hsv p hp']
  · show (s₂.mem.writeW (yA s₀) v).readW _ _ = _
    rw [Mem.readW_writeW_sep (hp.rY.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide),
      r₂.m.frame.readW (r := rR s₀) (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.rS) (by decide)]
  · show blockAt (s₂.mem.writeW (yA s₀) v) (yA s₀) = _
    rw [blockAt_eq, show (s₂.mem.writeW (yA s₀) v).readW (yA s₀) 128 = v from Mem.readW_writeW_self _ _ 16 v (by decide), ← hv, ← blockAt_eq, ← wd_mem, Offset.add_add, Offset.add_add, Offset.add_add,
      Offset.add_add]
    have bb : ∀ v : BitVec 32, bswap (bswap v) = v := Proof.Cmac.byteRev32_byteRev32
    have g : ∀ k < 64, s₂.mem.readW ((sP s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32 = a₁.m k := r₂.m.get
    rw [show 128 + 0 = 4 * 32 from rfl, show 128 + 4 = 4 * 33 from rfl, show 128 + 8 = 4 * 34 from rfl,
      show 128 + 12 = 4 * 35 from rfl, g 32 (by decide), g 33 (by decide), g 34 (by decide), g 35 (by decide), m0, m1, m2, m3,
      bb, bb, bb, bb]
    exact ha.y

theorem correct {s₀ : State} (hp : GPre s₀) :
    WP isa ghash s₀ fun s' => abiPreserved s₀ s' ∧ ghashX86.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nBlk s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (nBlk s₀ = 0)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nBlk s₀ = 0 := of_decide_eq_true h
    exact WP.block_nil (h0.symm ▸ hI)
  · have h0 : 0 < nBlk s₀ := Nat.pos_of_ne_zero (of_decide_eq_false h)
    let I : Nat → State → Prop := fun m s => ∃ i, m = nBlk s₀ - i ∧ i < nBlk s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, I m s → WP isa (.block body) s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nBlk s₀) s') ∨ (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hi hI) fun s' ⟨hI', hz'⟩ => ?_
      by_cases hl : nBlk s₀ - (i + 1) = 0
      · have : i + 1 = nBlk s₀ := by omega
        exact .inl ⟨by simp only [eval, hz', hl, decide_true, Option.map_some, Bool.not_true], this ▸ hI'⟩
      · exact .inr ⟨by simp only [eval, hz', hl, decide_false, Option.map_some, Bool.not_false], nBlk s₀ - (i + 1),
          by omega, i + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nBlk s₀) s₁ ⟨0, rfl, h0, hI⟩

theorem ghash_correct (s : State) (hs : ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.ghash s t s' ∧ abiPreserved s s' ∧ ghashX86.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (GPre.of hs)
  exact ⟨t, s', he, h.1, h.2⟩

theorem ghash_ct : ConstantTime isa ghashX86.pre ghashX86.pub Impl.Gcm.X86.ghash :=
  VG.Taint.constantTime (A := sseTaint) ghτ₀ (fun _ _ h₁ h₂ hp => gh_agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Gcm.X86
