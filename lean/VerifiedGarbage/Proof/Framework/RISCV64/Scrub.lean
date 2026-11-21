module

public import VerifiedGarbage.Impl.Scrub.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.TCB.RISCV64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Returning without secret residue (64-bit RISC-V)

`Verified.scrubAll`: code verified against a contract that `Sig.contract`
derives, whose frames use at most the contract's `stack` bytes
(`Code.riscv64Depth`), followed by `Impl.Scrub.RISCV64.scrubTail`
(`scrubAll`), is verified against the same contract and returns without secret
residue (`NoResidue`), as on x86-64 (`Proof/Framework/X86_64/Scrub.lean`).
The proof of the code is used as it is: what `scrubAll` adds is checked once,
here, for all code (`tail_run`): it zeroes the `stack` bytes below `sp` and
the caller-saved registers, and its trace depends only on `sp`. The code
itself must use no more stack than its contract reserves, call indirectly
only the functions of its tables of functions, whose addresses two runs agree
on (`tablesCall`), and its postcondition read the memory on return only
within the buffers (`PostOut`).

Everything the code leaves is then a function of what the two runs agree on:
the registers it does not clear are restored (`abiPreserved`), it changes no
memory outside the buffers but the stack it used (`Exec.stackFrame`), and
there the clearing's frames, once released, hold zero or what the unknowns
say replaces a released frame's bytes (`lose`, `wipeMem`): a function of
`sp` and of the unknowns the clearing starts from, which are the same in
both runs (`Exec.unknowns_agree`).
-/

@[expose] public section

open VG.Impl.Scrub.RISCV64

namespace VG.RISCV64

/-! ## Stack depth -/

/-- The bytes a frame's push moves `sp` down by. -/
def frameBytes : Instr → Nat
  | .push _ => 16
  | .alloc n => n
  | _ => 0

/-- How much stack below `sp` code uses at once, in bytes: its frames, of
registers (`push`) or of buffers (`alloc`). A call leaves its return address
in `ra`, not in memory. -/
def _root_.VG.Code.riscv64Depth : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max a.riscv64Depth b.riscv64Depth
  | .ite _ t e => max t.riscv64Depth e.riscv64Depth
  | .loop b _ => b.riscv64Depth
  | .call _ b => b.riscv64Depth
  | .frame i b _ => b.riscv64Depth + frameBytes i
  | .icall _ _ b n => max b.riscv64Depth n.riscv64Depth

namespace Scrub

/-- A frame's push: its region, at the head of `wr`, is the `frameBytes`
bytes below `sp`, and it changes memory only there. -/
theorem push_frame {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    s₁.wr = below s.sp (frameBytes i) :: s.wr ∧ s₁.sp = s.sp - BitVec.ofNat 64 (frameBytes i) ∧
      s₁.rd = s.rd ∧ s₁.gpr = s.gpr ∧ Frame [below s.sp (frameBytes i)] s.mem s₁.mem := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  · split at h <;> cases h
    exact ⟨rfl, rfl, rfl, rfl, Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (frame_contains _)⟩
  · split at h <;> cases h
    exact ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- A frame of `n` bytes is in the `d + n` bytes below `sp`. -/
theorem below_frameN (sp : Addr) (n d : Nat) (hn : d + n < 2 ^ 64) :
    Region.Sub (below sp n) (below sp (d + n)) :=
  below_sub (by omega_using []) hn

/-- The stack a frame's body uses is below the frame. -/
theorem below_bodyN (sp : Addr) (n d : Nat) :
    Region.Sub (below (sp - BitVec.ofNat 64 n) d) (below sp (d + n)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (d + n)) = x - (sp - BitVec.ofNat 64 n - BitVec.ofNat 64 d) by
    rw [BitVec.ofNat_add]; bv_omega]
  omega_using [hx]

/-- Code changes memory only within the regions it may write, and within
`c.riscv64Depth` bytes below `sp` (its frames). -/
theorem Exec.stackFrame {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hd : c.riscv64Depth < 2 ^ 64) :
    Frame (s.wr ++ [below s.sp c.riscv64Depth]) s.mem s'.mem := by
  induction h with
  | icall _ hc _ hr ih =>
    simp only [Code.riscv64Depth] at hd ⊢
    obtain ⟨-, w₁, p₁, m₁, -⟩ := call_eq hc
    rw [ret_eq hr]
    have := ih (by omega_using [hd])
    rw [w₁, p₁, m₁] at this
    exact Frame.below_mono this (by omega_using []) (by omega_using [hd])
  | icallNext _ _ _ ih =>
    simp only [Code.riscv64Depth] at hd ⊢
    exact Frame.below_mono (ih (by simp only [Code.riscv64Depth]; omega_using [hd]))
      (by simp only [Code.riscv64Depth]; omega_using []) (by omega_using [hd])
  | block h => exact Frame.mono (execBlock_regions h).2.2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [Code.riscv64Depth] at hd ⊢
    have f₁ := Frame.below_mono (ih₁ (by omega_using [hd])) (b := max c₁.riscv64Depth c₂.riscv64Depth)
      (by omega_using []) hd
    have f₂ := Frame.below_mono (ih₂ (by omega_using [hd])) (b := max c₁.riscv64Depth c₂.riscv64Depth)
      (by omega_using []) hd
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    rw [w₁, p₁] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [Code.riscv64Depth] at hd ⊢
    exact Frame.below_mono (ih (by omega_using [hd])) (by omega_using []) hd
  | iteF _ _ ih =>
    simp only [Code.riscv64Depth] at hd ⊢
    exact Frame.below_mono (ih (by omega_using [hd])) (by omega_using []) hd
  | loopExit _ _ ih => exact ih hd
  | loopNext h₁ _ _ ih₁ ih₂ =>
    have f₂ := ih₂ hd
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    rw [w₁, p₁] at f₂
    exact Frame.trans (ih₁ hd) f₂
  | call hc _ hr ih =>
    simp only [Code.riscv64Depth] at hd ⊢
    obtain ⟨-, w₁, p₁, m₁, -⟩ := call_eq hc
    rw [ret_eq hr]
    have := ih hd
    rwa [w₁, p₁, m₁] at this
  | @frame i _ b s₀ s₁ s₂ _ _ hp _ hq ih =>
    simp only [Code.riscv64Depth] at hd ⊢
    obtain ⟨w₁, p₁, -, -, f₀⟩ := push_frame hp
    obtain ⟨n, hn, f₂⟩ := pop_mem hq
    have hreg : (⟨s₁.sp, n⟩ : Region) = below s₀.sp (frameBytes i) := by
      rw [w₁, List.head?_cons, Option.some.injEq] at hn; exact hn.symm
    rw [hreg] at f₂
    have f₁ := ih (by omega_using [hd])
    rw [w₁, p₁] at f₁
    refine Frame.trans (Frame.trans (Frame.sub f₀ fun r hr => ?_) (Frame.sub f₁ fun r hr => ?_))
      (Frame.sub f₂ fun r hr => ?_)
    rotate_left 2
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_frameN _ _ _ hd⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_frameN _ _ _ hd⟩
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_frameN _ _ _ hd⟩
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_bodyN _ _ _⟩

/-! ## The clearing's run -/

/-- `m` with the bytes at offsets `lo` to `hi - 1` from `q` zeroed. -/
def zeroOn (q : Addr) (lo hi : Nat) (m : Mem) : Mem :=
  fun x => if lo ≤ (x - q).toNat ∧ (x - q).toNat < hi then 0 else m x

theorem off_lt (x p : Addr) (o n : Nat) (ho : o + n < 2 ^ 64) :
    (x - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ (x - p).toNat ∧ (x - p).toNat < o + n := by
  have e : (x - (p + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o = x - p := by bv_omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho])] at e'
  have h1 := (x - (p + BitVec.ofNat 64 o)).isLt
  have h2 := (x - p).isLt
  generalize (x - (p + BitVec.ofNat 64 o)).toNat = r at *
  generalize (x - p).toNat = d at *
  by_cases hc : r + o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc] at e'; omega_using [e']
  · rw [show r + o = (r + o - 2 ^ 64) + 2 ^ 64 by omega_using [hc], Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [ho, h1])] at e'
    omega_using [ho, h1, e', hc]

theorem toNat_add_of_lt (q : Addr) (o : Nat) (h : q.toNat + o < 2 ^ 64) :
    (q + BitVec.ofNat 64 o).toNat = q.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-- The trace of `stores k n` from `t1 = q`. -/
def storesTr (q : Addr) : Nat → Nat → List Leak
  | _, 0 => []
  | k, n + 1 => .addr (q + BitVec.ofNat 64 (8 * k)) :: storesTr q (k + 1) n

/-- `stores k n` zeroes the doublewords at offsets `8k` to `8(k + n) - 1`
from `t1 = q`, in a writable frame `⟨q, b⟩`. -/
theorem stores_run (q : Addr) (b : Nat) (hq : q.toNat % 8 = 0) (hb : b ≤ 2048)
    (hqb : q.toNat + b ≤ 2 ^ 64) :
    ∀ (n k : Nat) (u : State), 8 * (k + n) ≤ b → u.gpr .t0 = 0 → u.gpr .t1 = q → ⟨q, b⟩ ∈ u.wr →
      execBlock isa (stores k n) u = some ({ u with mem := zeroOn q (8 * k) (8 * (k + n)) u.mem },
        storesTr q k n)
  | 0, k, u, _, _, _, _ => by
    simp only [stores, execBlock, storesTr]
    congr
    cases u; simp only [State.mk.injEq, and_true, true_and]
    funext x; simp only [zeroOn, Nat.add_zero]; split
    · next h => omega_using [h.1, h.2]
    · rfl
  | n + 1, k, u, hk, h0, h1, hw => by
    have hlt : q.toNat + 8 * k < 2 ^ 64 := by omega_using [hk, hqb]
    have ha : (u.gpr .t1 + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
      rw [h1, toNat_add_of_lt q _ hlt]; omega_using [hq]
    have hc : InRegions u.wr (u.gpr .t1 + BitVec.ofNat 64 (8 * k)) 8 := by
      refine ⟨_, hw, ?_⟩
      simp only [Region.Contains]
      rw [h1, show q + BitVec.ofNat 64 (8 * k) - q = BitVec.ofNat 64 (8 * k) by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlt])]
      omega_using [hk]
    simp only [stores, execBlock, exec_store_d (by omega_using [hk, hb]) ha hc]
    rw [stores_run q b hq hb hqb n (k + 1) { u with mem := u.mem.writeW (u.gpr .t1 + BitVec.ofNat 64 (8 * k)) (u.gpr .t0) }
      (by omega_using [hk]) h0 h1 hw]
    have hm : zeroOn q (8 * (k + 1)) (8 * (k + 1 + n))
        (u.mem.writeW (u.gpr .t1 + BitVec.ofNat 64 (8 * k)) (u.gpr .t0)) =
        zeroOn q (8 * k) (8 * (k + (n + 1))) u.mem := by
      funext x
      have e := off_lt x q (8 * k) 8 (by omega_using [hk, hb])
      simp only [zeroOn, Mem.writeW, Mem.write, h0, h1, Nat.reduceDiv, Nat.reduceMul]
      generalize (x - (q + BitVec.ofNat 64 (8 * k))).toNat = r at e ⊢
      generalize (x - q).toNat = d at e ⊢
      repeat' split
      all_goals first | (exfalso; omega) | rfl | (simp; done)
    simp only [Option.map_some, isa, addrs, h1, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, storesTr]
    rw [h1] at hm
    rw [hm]

theorem toNat_sub_ofNat (p : Addr) (b : Nat) (h : b ≤ p.toNat) :
    (p - BitVec.ofNat 64 b).toNat = p.toNat - b := by
  have := p.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega_using [h, this]),
    show 2 ^ 64 - b + p.toNat = (p.toNat - b) + 2 ^ 64 by omega_using [h, this], Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [this])]

/-- The trace of `wipe cs` from `sp = p`. -/
def wipeTr : List Nat → Addr → List Leak
  | [], _ => []
  | b :: bs, p => storesTr (p - BitVec.ofNat 64 b) 0 (b / 8) ++ wipeTr bs (p - BitVec.ofNat 64 b)

/-- How many unknowns the frames of `wipe cs` use when they are released. -/
def wipeK : List Nat → Nat
  | [] => 0
  | b :: bs => wipeK bs + b / 4

/-- What `wipe cs` from `sp = p`, from the unknowns `U`, leaves in the
`cs.sum` bytes below `p`: zero, or what replaces a byte of a released frame
(`lose`). A function of `p` and `U` alone. -/
def wipeZ : List Nat → Addr → (Nat → BitVec 64) → Addr → BitVec 8
  | [], _, _, _ => 0
  | b :: bs, p, U, x =>
    if (x - (p - BitVec.ofNat 64 b)).toNat < b then
      lose (fun _ => 0) (p - BitVec.ofNat 64 b) b (fun n => U (n + wipeK bs)) x
    else wipeZ bs (p - BitVec.ofNat 64 b) U x

/-- The memory `wipe cs` leaves from `sp = p`, the unknowns `U` and the
memory `m`: `wipeZ` below `p`, `m` elsewhere. -/
def wipeMem (cs : List Nat) (p : Addr) (U : Nat → BitVec 64) (m : Mem) : Mem :=
  fun x => if (x - (p - BitVec.ofNat 64 cs.sum)).toNat < cs.sum then wipeZ cs p U x else m x

/-- A frame of the wipe, then the frames below it. -/
theorem wipeMem_cons (p : Addr) (b : Nat) (bs : List Nat) (U : Nat → BitVec 64) (m : Mem)
    (h : b + bs.sum < 2 ^ 64) :
    lose (wipeMem bs (p - BitVec.ofNat 64 b) U (zeroOn (p - BitVec.ofNat 64 b) 0 b m))
      (p - BitVec.ofNat 64 b) b (fun n => U (n + wipeK bs)) = wipeMem (b :: bs) p U m := by
  have e1 : p - BitVec.ofNat 64 b - BitVec.ofNat 64 bs.sum = p - BitVec.ofNat 64 (b + bs.sum) := by
    rw [BitVec.ofNat_add]; bv_omega
  have e2 : p - BitVec.ofNat 64 b = p - BitVec.ofNat 64 (b + bs.sum) + BitVec.ofNat 64 bs.sum := by
    rw [BitVec.ofNat_add]; bv_omega
  funext x
  have e := off_lt x (p - BitVec.ofNat 64 (b + bs.sum)) bs.sum b (by omega_using [h])
  simp only [wipeMem, wipeZ, lose, zeroOn, List.sum_cons, Nat.zero_le, true_and, e1]
  rw [e2]
  generalize (x - (p - BitVec.ofNat 64 (b + bs.sum) + BitVec.ofNat 64 bs.sum)).toNat = r at e ⊢
  generalize (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat = d at e ⊢
  repeat' split
  all_goals first | (exfalso; omega) | rfl

/-- `wipe cs` leaves `wipeMem` in memory, uses `wipeK cs` unknowns, and
changes no register but `t1`. -/
theorem wipe_run : ∀ (cs : List Nat) (u : State), (∀ b ∈ cs, 0 < b ∧ b ≤ 2048 ∧ b % 16 = 0) →
    cs.sum ≤ u.sp.toNat → u.sp.toNat % 16 = 0 → u.gpr .t0 = 0 →
    ∃ g : Reg → BitVec 64, (∀ r, r ≠ .t1 → g r = u.gpr r) ∧
      Exec isa (wipe cs) u (wipeTr cs u.sp)
        { u with
          gpr := g, mem := wipeMem cs u.sp u.unknowns u.mem,
          unknowns := fun n => u.unknowns (n + wipeK cs) }
  | [], u, _, _, _, _ => by
    refine ⟨u.gpr, fun _ _ => rfl, ?_⟩
    have : ({ u with
        gpr := u.gpr, mem := wipeMem [] u.sp u.unknowns u.mem,
        unknowns := fun n => u.unknowns (n + wipeK []) } : State) = u := by
      cases u; simp only [State.mk.injEq, and_true, true_and]
      refine ⟨?_, ?_⟩
      · funext x; simp [wipeMem]
      · funext n; simp [wipeK]
    simp only [wipe, wipeTr]
    rw [this]; exact .block rfl
  | b :: bs, u, hv, hs, h16, h0 => by
    obtain ⟨hb0, hb, hb16⟩ := hv b List.mem_cons_self
    have hbs : ∀ b ∈ bs, 0 < b ∧ b ≤ 2048 ∧ b % 16 = 0 := fun b' h => hv b' (List.mem_cons_of_mem _ h)
    simp only [List.sum_cons] at hs
    have hp := u.sp.isLt
    have hq : (u.sp - BitVec.ofNat 64 b).toNat = u.sp.toNat - b := toNat_sub_ofNat _ _ (by omega_using [hs])
    have hpush : isa.push (.alloc b) u =
        some { u with sp := u.sp - BitVec.ofNat 64 b, wr := ⟨u.sp - BitVec.ofNat 64 b, b⟩ :: u.wr } := by
      have h1 : b ≤ 4064 := by omega_using [hb]
      have h2 : b ≤ u.sp.toNat := by omega_using [hs]
      simp only [isa, push, hb0, h1, hb16, h2, and_self, ite_true]
    generalize hs₁ : ({ u with sp := u.sp - BitVec.ofNat 64 b, wr := ⟨u.sp - BitVec.ofNat 64 b, b⟩ :: u.wr } :
      State) = s₁ at hpush
    have hs₁sp : s₁.sp = u.sp - BitVec.ofNat 64 b := by rw [← hs₁]
    have hs₁wr : s₁.wr = ⟨u.sp - BitVec.ofNat 64 b, b⟩ :: u.wr := by rw [← hs₁]
    have hs₁g : s₁.gpr = u.gpr := by rw [← hs₁]
    -- The frame's stores.
    have hst := stores_run (u.sp - BitVec.ofNat 64 b) b (by omega_using [hq, h16, hb16, hs]) hb
      (by omega_using [hq, hs, hp]) (b / 8) 0 (s₁.write .t1 (s₁.sp + BitVec.ofNat 64 0))
      (by omega_using [hb16]) (by rw [RegUpd.gpr_write_of_ne _ _ (by decide), hs₁g, h0])
      (by rw [RegUpd.gpr_write_self, hs₁sp]; simp)
      (by rw [RegUpd.wr_write, hs₁wr]; exact List.mem_cons_self)
    have hblk : execBlock isa (.addSp .t1 0 :: stores 0 (b / 8)) s₁ =
        some ({ s₁.write .t1 (s₁.sp + BitVec.ofNat 64 0) with
          mem := zeroOn (u.sp - BitVec.ofNat 64 b) (8 * 0) (8 * (0 + b / 8)) s₁.mem },
          storesTr (u.sp - BitVec.ofNat 64 b) 0 (b / 8)) := by
      simp only [execBlock, isa, exec_addSp (show 0 < 2048 by decide), hst, Option.map_some, addrs,
        List.map_nil, List.nil_append, RegUpd.mem_write]
    generalize hs₂ : ({ s₁.write .t1 (s₁.sp + BitVec.ofNat 64 0) with
      mem := zeroOn (u.sp - BitVec.ofNat 64 b) (8 * 0) (8 * (0 + b / 8)) s₁.mem } : State) = s₂ at hblk
    have hs₂sp : s₂.sp = u.sp - BitVec.ofNat 64 b := by rw [← hs₂]; exact hs₁sp
    have hs₂g0 : s₂.gpr .t0 = 0 := by
      rw [← hs₂]; simp [State.write, hs₁g, h0]
    obtain ⟨g, hg, he⟩ := wipe_run bs s₂ hbs (by rw [hs₂sp, hq]; omega_using [hs])
      (by rw [hs₂sp, hq]; omega_using [h16, hb16, hs]) hs₂g0
    generalize hs₃ : ({ s₂ with
      gpr := g, mem := wipeMem bs s₂.sp s₂.unknowns s₂.mem,
      unknowns := fun n => s₂.unknowns (n + wipeK bs) } : State) = s₃ at he
    have hpop : isa.pop (.free b) s₁ s₃ = some { s₃ with
        sp := s₃.sp + BitVec.ofNat 64 b, wr := s₃.wr.tail,
        mem := lose s₃.mem s₃.sp b s₃.unknowns, unknowns := fun n => s₃.unknowns (n + b / 4) } := by
      have h1 : b ≤ 4064 := by omega_using [hb]
      have hw : s₃.wr = s₁.wr := by rw [← hs₃, ← hs₂]; rfl
      have hsp : s₃.sp = s₁.sp := by rw [← hs₃]; exact hs₂sp.trans hs₁sp.symm
      simp only [isa, pop, hb0, h1, hb16, hsp, hw, hs₁wr, hs₁sp, List.head?_cons, and_self, ite_true]
    have ef := Exec.frame (M := isa) (i := Instr.alloc b) (j := Instr.free b) hpush (.seq (.block hblk) he) hpop
    refine ⟨g, fun r hr => ?_, ?_⟩
    · rw [hg r hr, ← hs₂]
      exact (RegUpd.gpr_write_of_ne _ _ hr).trans (by rw [hs₁g])
    · have et : (List.map Leak.addr (isa.addrs (.alloc b) u) ++
          (storesTr (u.sp - BitVec.ofNat 64 b) 0 (b / 8) ++ wipeTr bs s₂.sp) ++
          List.map Leak.addr (isa.addrs (.free b) s₃)) =
          wipeTr (b :: bs) u.sp := by
        simp only [addrs, List.map_nil, List.nil_append, List.append_nil, wipeTr, hs₂sp]
      rw [et] at ef
      have es : ({ s₃ with
          sp := s₃.sp + BitVec.ofNat 64 b, wr := s₃.wr.tail,
          mem := lose s₃.mem s₃.sp b s₃.unknowns, unknowns := fun n => s₃.unknowns (n + b / 4) } : State) =
          { u with
            gpr := g, mem := wipeMem (b :: bs) u.sp u.unknowns u.mem,
            unknowns := fun n => u.unknowns (n + wipeK (b :: bs)) } := by
        subst hs₃ hs₂ hs₁
        have hz := wipeMem_cons u.sp b bs u.unknowns u.mem (by omega_using [hs, hp])
        simp only [Nat.mul_zero, show 8 * (0 + b / 8) = b by omega_using [hb16]] at hz ⊢
        cases u
        simp only [State.write, List.tail_cons,
          BitVec.sub_add_cancel, State.mk.injEq, true_and, and_true] at hz ⊢
        refine ⟨hz, ?_⟩
        funext n; simp only [wipeK]; congr 1; omega
      rw [es] at ef
      exact ef

/-- What `retFix rb` leaves in `a0`. -/
def fixA (rb : Nat) (x : BitVec 64) : BitVec 64 :=
  if rb = 0 then 0 else if rb < 64 then (x <<< (64 - rb)) >>> (64 - rb) else x

theorem fixA_low {rb : Nat} (hrb : rb ≤ 64) (x : BitVec 64) : (fixA rb x).setWidth rb = x.setWidth rb := by
  unfold fixA
  split
  · next h => subst h; exact BitVec.eq_nil _ |>.trans (BitVec.eq_nil _).symm
  · split
    · ext i hi
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      simp
      omega
    · next h₁ h₂ => rfl

theorem fixA_hi {rb : Nat} (hrb : rb ≤ 64) (x : BitVec 64) : fixA rb x >>> rb = 0 := by
  unfold fixA
  split
  · simp
  · split
    · ext i hi
      simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
      simp
      omega
    · next h₁ h₂ =>
      obtain rfl : rb = 64 := by omega
      ext i hi; simp

/-- The registers after the clearing, from `g`. -/
def finG (rb : Nat) (g : Reg → BitVec 64) : Reg → BitVec 64 :=
  fun r => if r ∈ scratchRegs then 0 else if r = .a0 then fixA rb (g .a0) else g r

theorem zeroRs_run : ∀ (rs : List Reg) (u : State),
    execBlock isa (rs.map zeroR) u = some ({ u with gpr := fun r => if r ∈ rs then 0 else u.gpr r }, [])
  | [], u => by simp only [List.map_nil, execBlock, List.not_mem_nil, ite_false]
  | r :: rs, u => by
    simp only [List.map_cons, execBlock, zeroR, isa, exec_li (show imm12 0 by decide)]
    rw [zeroRs_run rs]
    simp only [Option.map_some, addrs, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq,
      and_true]
    cases u
    simp only [State.write, State.mk.injEq, and_true]
    funext r'
    by_cases h₁ : r' ∈ rs
    · simp [h₁]
    · by_cases h₂ : r' = r
      · subst h₂; simp
      · simp [h₁, h₂]

theorem retFix_run {rb : Nat} (hrb : rb ≤ 64) (u : State) :
    execBlock isa (retFix rb) u =
      some ({ u with gpr := fun r => if r = .a0 then fixA rb (u.gpr .a0) else u.gpr r }, []) := by
  unfold retFix fixA
  split
  · next h =>
    rw [show [zeroR .a0] = [Reg.a0].map zeroR from rfl, zeroRs_run]
    simp only [List.mem_singleton]
  · split
    · next h₁ h₂ =>
      simp only [ite_true, execBlock, isa, exec, show 64 - rb < 64 by omega, ite_true,
        Option.map_some, addrs, List.map_nil, List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
      cases u
      simp only [State.write, State.mk.injEq, and_true]
      funext r'
      by_cases h : r' = .a0 <;> simp [h]
    · next h₁ h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq, and_true]
      cases u
      simp only [State.mk.injEq, and_true]
      funext r'
      by_cases h : r' = .a0
      · subst h; rfl
      · simp [h]

/-- The trace of `scrubTail rb cs` from `sp = p`: a function of `p`. -/
def tailTr (cs : List Nat) (p : Addr) : List Leak := [] ++ (wipeTr cs p ++ [])

/-- The clearing's run, from a state whose `sp` is aligned and has `cs.sum`
bytes below it: it leaves there what `wipeMem` says, and in the registers
what `finG` says. -/
theorem tail_run {rb : Nat} (hrb : rb ≤ 64) {cs : List Nat} (hv : ∀ b ∈ cs, 0 < b ∧ b ≤ 2048 ∧ b % 16 = 0)
    (u : State) (hs : cs.sum ≤ u.sp.toNat) (h16 : u.sp.toNat % 16 = 0) :
    Exec isa (scrubTail rb cs) u (tailTr cs u.sp)
      { u with
        gpr := finG rb u.gpr, mem := wipeMem cs u.sp u.unknowns u.mem,
        unknowns := fun n => u.unknowns (n + wipeK cs) } := by
  have h₀ : execBlock isa [zeroR .t0] u =
      some ({ u with gpr := fun r => if r ∈ [Reg.t0] then 0 else u.gpr r }, []) := zeroRs_run [.t0] u
  generalize hu₁ : ({ u with gpr := fun r => if r ∈ [Reg.t0] then 0 else u.gpr r } : State) = u₁ at h₀
  have hsp : u₁.sp = u.sp := by rw [← hu₁]
  have hmem : u₁.mem = u.mem := by rw [← hu₁]
  have hunk : u₁.unknowns = u.unknowns := by rw [← hu₁]
  have hg₁ : ∀ r, r ≠ .t0 → u₁.gpr r = u.gpr r := fun r hr => by rw [← hu₁]; simp [hr]
  obtain ⟨g, hg, hw⟩ := wipe_run cs u₁ hv (hsp ▸ hs) (hsp ▸ h16) (by rw [← hu₁]; simp)
  have hc := execBlock_append (M := isa) (retFix rb) (scratchRegs.map zeroR)
    { u₁ with
      gpr := g, mem := wipeMem cs u₁.sp u₁.unknowns u₁.mem,
      unknowns := fun n => u₁.unknowns (n + wipeK cs) }
  rw [retFix_run hrb, Option.bind_some, zeroRs_run] at hc
  have e := Exec.seq (.block h₀) (.seq hw (.block hc))
  have eg : (fun r => if r ∈ scratchRegs then 0 else
      (fun r => if r = Reg.a0 then fixA rb (g .a0) else g r) r) = finG rb u.gpr := by
    funext r
    simp only [finG]
    by_cases h : r ∈ scratchRegs
    · simp [h]
    · have h0 : r ≠ .t0 := fun e => h (e ▸ by decide)
      have h1 : r ≠ .t1 := fun e => h (e ▸ by decide)
      simp only [h, ite_false, hg r h1, hg₁ r h0, hg .a0 (by decide), hg₁ .a0 (by decide)]
  have et : ([] ++ (wipeTr cs u₁.sp ++ ([] ++ []))) = tailTr cs u.sp := by
    simp only [hsp, tailTr, List.nil_append]
  simp only at e
  rw [eg, et, hsp, hmem, hunk] at e
  subst hu₁
  exact e

theorem chunksAux_spec : ∀ f n, n / 2048 < f →
    (chunksAux f n).sum = n ∧ ∀ b ∈ chunksAux f n, 0 < b ∧ b ≤ 2048 ∧ (n % 16 = 0 → b % 16 = 0)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => ⟨rfl, fun _ h => by simp [chunksAux] at h⟩
  | f + 1, n + 1, h => by
    simp only [chunksAux]
    split
    · exact ⟨by simp, fun b hb => by simp at hb; subst hb; omega_arith⟩
    · obtain ⟨hs, hv⟩ := chunksAux_spec f (n + 1 - 2048) (by omega_arith)
      refine ⟨by rw [List.sum_cons, hs]; omega_arith, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · omega_using []
      · have := hv b hb; omega_using [this]

theorem chunks_sum (n : Nat) : (chunks n).sum = n := (chunksAux_spec _ n (by omega_using [])).1

theorem chunks_valid {n : Nat} (h16 : n % 16 = 0) : ∀ b ∈ chunks n, 0 < b ∧ b ≤ 2048 ∧ b % 16 = 0 :=
  fun b hb => by have := (chunksAux_spec _ n (by omega_using [])).2 b hb; omega_using [h16, this]

/-! ## What `Sig.contract` gives -/

/-- What `Verified.scrubAll` needs of the calling convention a contract is for:
`abi`'s, possibly with tables of constants (`Abi.withConsts`), which add
readable regions apart from the stack the function uses, and with tables of
functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 64
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → s.sp.toNat % 16 = 0 ∧ (n = 0 ∨ n ≤ s.sp.toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.sp = s₂.sp
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .a0
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  have h8 : argRegs.length = 8 := rfl
  simp only [abi] at h
  split at h
  · next hl => cases h; simp only [List.length_map, List.length_take]; omega_using [hl]
  · next hl =>
    split at h
    · cases h; simp only [List.length_append, List.length_map, List.length_range]; omega_using [hl]
    · cases h

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    s.sp.toNat % 16 = 0 ∧ (n = 0 ∨ n ≤ s.sp.toNat) := by
  obtain ⟨h16, hn, -⟩ := h
  refine ⟨h16, ?_⟩
  cases n with
  | zero => exact .inl rfl
  | succ n => exact .inr hn

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ _ h => ⟨(abi_wf_stack h).1, (abi_wf_stack h).2, fun _ hr hn => absurd hr hn⟩,
    fun _ _ h => h, fun _ => rfl, fun _ => rfl, fun _ _ h => h, abi_args_len⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1, fun _ => rfl, fun _ => rfl,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨(abi_wf_stack hw).1, (abi_wf_stack hw).2, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.mem, hA.ret, hA.rdSub, hA.argsLen⟩

/-- The calling convention of every RISC-V artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi ((abi.withConsts cs).withTables sig ts) :=
  (ScrubAbi.consts cs).tables sig ts

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- The stack the function may use is aligned, does not wrap around, and is
apart from every region it may access. -/
theorem contract_pre_scrub (hA : ScrubAbi A) {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    s.sp.toNat % 16 = 0 ∧ (stack = 0 ∨ stack ≤ s.sp.toNat) ∧
      ∀ r ∈ s.rd ++ s.wr, stack ≠ 0 → (below s.sp stack).Disjoint r := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨h16, hst, hcon⟩ := hA.wf _ _ _ hwf
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have key : ∀ r ∈ s.rd ++ s.wr, ∀ q ∈ abi.reserved stack s, q.Disjoint r := by
    intro r hr q hq
    rcases List.mem_append.mp hr with hr | hr
    · by_cases hn : r ∈ A.rd s
      · rw [hrd] at hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        exact hres' q hq a (List.mem_filter.mp ha).1
      · exact hcon r hr hn q hq
    · rw [← hA.wr, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hres' q hq a (List.mem_filter.mp ha).1
  refine ⟨h16, hst, fun r hr hn => key r hr _ ?_⟩
  cases stack with
  | zero => exact absurd rfl hn
  | succ n => simp [abi, stackBelow]

theorem contract_pub_sp (hA : ScrubAbi A) {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.sp = s₂.sp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

end

/-! ## The result -/

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits. -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .a0).setWidth rb = (u.gpr .a0).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds. -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-! ## Two runs use the same unknowns

A released frame's bytes are the unknowns' (`lose`), so the clearing leaves
the same bytes in two runs only if it starts from the same unknowns. Two
runs of code with the same trace, whose functions called indirectly have the
same addresses in both, do: each call, and each frame's release, uses a
number of unknowns its instruction fixes, and the trace says which way each
branch went and which function each indirect call called
(`Exec.unknowns_agree`), as on AArch64 (`AArch64.Scrub.Exec.unknowns_agreeS`). -/

/-- The functions `c` may call indirectly. -/
def inames : Prog isa → List String
  | .block _ => []
  | .seq a b => inames a ++ inames b
  | .ite _ t e => inames t ++ inames e
  | .loop b _ => inames b
  | .call _ b => inames b
  | .frame _ b _ => inames b
  | .icall _ n b nx => n :: inames b ++ inames nx

/-- The functions the tables `ts` name. -/
def tableFns (ts : List (String × List FnTable)) : List String := ts.flatMap fun t => t.2.flatMap (·.fns)

/-- The code calls indirectly only the functions of the tables `ts`, whose
addresses two runs agree on (`tables_pub_syms`). -/
def tablesCall (c : Prog isa) (ts : List (String × List FnTable)) : Bool :=
  (inames c).all fun f => decide (f ∈ tableFns ts)

theorem addrs_length (i : Instr) (s s' : State) : (addrs i s).length = (addrs i s').length := by
  cases i <;> rfl

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns := by
  unfold exec at h
  split at h
  all_goals first
    | (cases h; rfl)
    | (split at h <;> first | (cases h; rfl) | cases h)
    | (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
       obtain ⟨_, -, _, -, rfl⟩ := h; rfl)
    | (simp only [Option.bind_eq_some_iff, State.store] at h
       obtain ⟨_, -, h⟩ := h
       split at h <;> first | (cases h; rfl) | cases h)
    | cases h

theorem execBlock_unknowns : ∀ {is : List Instr} {s₁ s₂ a b : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (a, t₁) → execBlock isa is s₂ = some (b, t₂) →
      t₁.length = t₂.length ∧ a.unknowns = s₁.unknowns ∧ b.unknowns = s₂.unknowns
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, rfl, rfl⟩
  | i :: is, s₁, s₂, a, b, t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    cases e₁ : exec i s₁ with
    | none => rw [e₁] at h₁; cases h₁
    | some u₁ =>
      cases e₂ : exec i s₂ with
      | none => rw [e₂] at h₂; cases h₂
      | some u₂ =>
        rw [e₁] at h₁; rw [e₂] at h₂
        obtain ⟨p₁, hp₁, hq₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, hq₂⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₂
        obtain ⟨hl, ha, hb⟩ := execBlock_unknowns (s₁ := u₁) (s₂ := u₂) (by rw [hp₁]) (by rw [hp₂])
        refine ⟨?_, ha.trans (exec_unknowns e₁), hb.trans (exec_unknowns e₂)⟩
        simp only [List.length_append, List.length_map, hl, addrs_length i s₁ s₂]

theorem push_unknowns {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.unknowns = s.unknowns := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

/-- The unknowns a frame's release uses. -/
def popK : Instr → Nat
  | .pop _ => 4
  | .free b => b / 4
  | _ => 0

theorem pop_unknowns {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.unknowns = fun n => s₂.unknowns (n + popK j) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

theorem call_unknowns {s s₁ : State} (h : isa.call s = some s₁) :
    s₁.unknowns = fun n => s.unknowns (n + 8) := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem call_syms {s s₁ : State} (h : isa.call s = some s₁) : s₁.syms = s.syms := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem branch_ne {r₁ r₂ : List Leak} : Leak.branch true :: r₁ ≠ Leak.branch false :: r₂ := by
  intro h; cases h

/-- The trace of an indirect call: the addresses its instruction reads, then
the address it calls. -/
theorem icall_trace {i : Instr} {n : String} {b nx : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (.icall i n b nx) s t s') :
    ∃ a rest, isa.icall i s = some a ∧ t = (isa.addrs i s).map .addr ++ .addr a :: rest := by
  cases e with
  | icall h₁ _ _ _ => exact ⟨_, _, h₁, rfl⟩
  | icallNext _ _ e' => exact icall_trace e'

/-- Two runs of code from the same unknowns, whose functions called
indirectly have the same addresses (`inames`), one of whose traces is a
prefix of the other's continued, have the same trace and end with the same
unknowns: each call and each frame's release uses a number of unknowns its
instruction fixes, and the trace says which way each branch went and which
function each indirect call called. -/
theorem Exec.unknowns_agree {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ : List Leak} (r₁ r₂ : List Leak), Exec isa c s₂ t₂ s₂' →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) →
      s₁.unknowns = s₂.unknowns → t₁ ++ r₁ = t₂ ++ r₂ → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h₁ =>
    intro _ _ _ r₁ r₂ e₂ _ hu ht
    cases e₂ with
    | block h₂ =>
      obtain ⟨hl, ha, hb⟩ := execBlock_unknowns h₁ h₂
      exact ⟨(List.append_inj ht hl).1, ha.trans (hu.trans hb.symm)⟩
  | seq x₁ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    simp only [inames, List.mem_append] at hf
    cases e₂ with
    | seq a₂ b₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ _ _ a₂ (fun n hn => hf n (.inl hn)) hu ht
      obtain ⟨rfl, hu''⟩ := ih₂ _ _ b₂
        (fun n hn => by rw [Exec.syms x₁, Exec.syms a₂]; exact hf n (.inr hn)) hu' (List.append_cancel_left ht)
      exact ⟨rfl, hu''⟩
  | iteT _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | iteT _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ a₂ (fun n hn => hf n (List.mem_append_left _ hn)) hu ht
      exact ⟨rfl, hu'⟩
    | iteF _ _ => exact absurd ht branch_ne
  | iteF _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | iteT _ _ => exact absurd ht.symm branch_ne
    | iteF _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ a₂ (fun n hn => hf n (List.mem_append_right _ hn)) hu ht
      exact ⟨rfl, hu'⟩
  | loopExit _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ hf hu ht
      exact ⟨rfl, hu'⟩
    | loopNext b₂ _ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih _ _ b₂ hf hu ht
      exact absurd (List.append_cancel_left ht).symm branch_ne
  | loopNext x₁ _ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih₁ _ _ b₂ hf hu ht
      exact absurd (List.append_cancel_left ht) branch_ne
    | loopNext b₂ _ n₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ _ _ b₂ hf hu ht
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨rfl, hu''⟩ := ih₂ _ _ n₂ (by rw [Exec.syms x₁, Exec.syms b₂]; exact hf) hu' ht'
      exact ⟨rfl, hu''⟩
  | call hc₁ _ hr ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | call hc₂ b₂ hr₂ =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ (by rw [call_syms hc₁, call_syms hc₂]; exact hf)
        (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht
      rw [ret_eq hr, ret_eq hr₂]
      exact ⟨rfl, hu'⟩
  | @frame i j _ s₀ _ s₂ _ _ hp _ hq ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | @frame _ _ _ _ _ s₂' _ _ hp₂ b₂ hq₂ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map, addrs_length i s₀ s₀']
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ (by rw [push_syms hp, push_syms hp₂]; exact hf)
        (by rw [push_unknowns hp, push_unknowns hp₂, hu]) ht'
      have hl' : (List.map Leak.addr (isa.addrs j s₂)).length = (List.map Leak.addr (isa.addrs j s₂')).length := by
        simp only [List.length_map, addrs_length j s₂ s₂']
      have h₃ := (List.append_inj (List.append_cancel_left ht') hl').1
      refine ⟨by rw [h₀, h₃], ?_⟩
      rw [pop_unknowns hq, pop_unknowns hq₂, hu']
  | @icall i _ _ _ s₀ _ s₂ _ _ hi₁ hc₁ _ hr₁ ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    have hn := hf _ (List.mem_cons_self ..)
    cases e₂ with
    | @icall _ _ _ _ _ _ s₂' _ _ hi₂ hc₂ x₂ hr₂ =>
      simp only [List.append_assoc, List.cons_append] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map, addrs_length i s₀ s₀']
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      simp only [List.cons.injEq] at ht'
      obtain ⟨ha, ht'⟩ := ht'
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht' ⊢
      obtain ⟨rfl, hu'⟩ := ih _ _ x₂ (fun m hm => by
        rw [call_syms hc₁, call_syms hc₂]; exact hf m (by simp [inames, hm]))
        (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht'
      refine ⟨by rw [h₀, ha], ?_⟩
      rw [ret_eq hr₁, ret_eq hr₂]; exact hu'
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1]; exact hn
  | icallNext hi₁ hne₁ x₁ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      exact ih _ _ x₂ (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))) hu ht
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := List.append_inj ht (by simp only [List.length_map]; exact addrs_length _ _ _)
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

/-- The state after the clearing of `stack` bytes below `p`, from `u`. -/
def finState (rb stack : Nat) (p : Addr) (u : State) : State :=
  { u with
    gpr := finG rb u.gpr, mem := wipeMem (chunks stack) p u.unknowns u.mem,
    unknowns := fun n => u.unknowns (n + wipeK (chunks stack)) }

theorem not_scratch_preserved : ∀ r ∈ preserved, r ∉ scratchRegs ∧ r ≠ .a0 := by decide

theorem below_contains_iff (sp x : Addr) (n : Nat) :
    (below sp n).Contains x 1 ↔ (x - (sp - BitVec.ofNat 64 n)).toNat < n := by
  simp only [Region.Contains]; omega_using []

theorem wipeMem_below (cs : List Nat) (sp x : Addr) (U : Nat → BitVec 64) (m : Mem) :
    wipeMem cs sp U m x = if (below sp cs.sum).Contains x 1 then wipeZ cs sp U x else m x := by
  simp only [wipeMem, below_contains_iff]

/-- Code verified against a contract that `Sig.contract` derives, whose
frames use at most `stack` bytes, run by `scrubAll`, which clears the `stack`
bytes below `sp` and the caller-saved registers: verified against the same
contract, and without secret residue, if the postcondition reads the memory
on return only within the buffers (`hpost`). -/
theorem Verified.scrubAll {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa}
    (hA : ScrubAbi A) (h : Verified target c (sig.contract A pre post wa stack leak))
    (hd : c.riscv64Depth ≤ stack) (hst : stack < 2 ^ 64) (h16 : stack % 16 = 0)
    (hsy : ∀ s₁ s₂, (sig.contract A pre post wa stack leak).pub s₁ s₂ →
      ∀ n ∈ inames c, s₁.syms n = s₂.syms n) (hrb : sig.retBits A.ptrBits ≤ 64)
    (hpost : PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) :
    Verified target (Impl.Scrub.RISCV64.scrubAll (sig.retBits A.ptrBits) stack c)
        (sig.contract A pre post wa stack leak) ∧
      NoResidue (Impl.Scrub.RISCV64.scrubAll (sig.retBits A.ptrBits) stack c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have hv := chunks_valid h16
  -- What a run of `c` gives.
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧ u.sp = s.sp := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    exact ⟨ha, hp, ha.2.1⟩
  -- The clearing's run after it.
  have tail : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      Exec isa (scrubTail (sig.retBits A.ptrBits) (chunks stack)) u (tailTr (chunks stack) s.sp)
        (finState (sig.retBits A.ptrBits) stack s.sp u) := by
    intro s t u hs he
    obtain ⟨h16s, hsts, -⟩ := contract_pre_scrub hA hs
    obtain ⟨-, -, hsp⟩ := run s t u hs he
    have e := tail_run hrb hv u (by rw [chunks_sum, hsp]; rcases hsts with h0 | h0 <;> omega_using [h0])
      (by rw [hsp]; exact h16s)
    have e' : Exec isa (scrubTail (sig.retBits A.ptrBits) (chunks stack)) u (tailTr (chunks stack) u.sp)
        (finState (sig.retBits A.ptrBits) stack u.sp u) := e
    rw [hsp] at e'
    exact e'
  -- The buffers are apart from the stack the clearing wipes.
  have outB : ∀ s, (sig.contract A pre post wa stack leak).pre s → ∀ x,
      (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → ¬ (below s.sp stack).Contains x 1 := by
    intro s hs x ⟨r, hr, hx⟩ hb
    by_cases h0 : stack = 0
    · subst h0; simp [Region.Contains] at hb
    · exact (contract_pre_scrub hA hs).2.2 r hr h0 x hb hx
  have hdep : c.riscv64Depth < 2 ^ 64 := by omega_using [hd, hst]
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hsp⟩ := run s t u hs he
    refine ⟨_, _, .seq he (tail s t u hs he), ⟨fun r hr => ?_, hsp, ?_⟩, ?_⟩
    · obtain ⟨h1, h2⟩ := not_scratch_preserved r hr
      simp only [finState, finG, h1, h2, ite_false]
      exact ha.1 r hr
    · show finG (sig.retBits A.ptrBits) u.gpr .ra = _
      simp only [finG, show Reg.ra ∉ scratchRegs by decide, ite_false, show Reg.ra ≠ .a0 by decide]
      exact ha.2.2
    · refine hpost s u _ hs hq (fun x hx => ?_) ?_
      · show wipeMem (chunks stack) s.sp u.unknowns u.mem x = u.mem x
        rw [wipeMem_below, chunks_sum]
        simp only [outB s hs x hx, ite_false]
      · show (finG (sig.retBits A.ptrBits) u.gpr .a0).setWidth _ = _
        simp only [finG, show Reg.a0 ∉ scratchRegs by decide, ite_false, ite_true]
        exact fixA_low hrb _
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨rfl, -⟩ := Exec.det b₁ (tail s₁ _ _ h₁ a₁)
    obtain ⟨rfl, -⟩ := Exec.det b₂ (tail s₂ _ _ h₂ a₂)
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_sp hA hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨-, rfl⟩ := Exec.det b₁ (tail s₁ _ _ h₁ a₁)
    obtain ⟨-, rfl⟩ := Exec.det b₂ (tail s₂ _ _ h₂ a₂)
    obtain ⟨ha₁, -, hsp₁⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, hsp₂⟩ := run s₂ _ _ h₂ a₂
    obtain ⟨hrd, hwr, hg, -, hsp, hm⟩ := ho
    obtain ⟨rd₁, wr₁, -⟩ := Exec.rdwr a₁
    obtain ⟨rd₂, wr₂, -⟩ := Exec.rdwr a₂
    -- The two runs of `c` have the same trace, so they end with the same unknowns.
    obtain ⟨-, hU⟩ := Exec.unknowns_agree a₁ [] [] a₂ (hsy _ _ hp) hun
      (by rw [List.append_nil, List.append_nil]; exact hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂)
    have keep : ∀ r, r ∉ scratchRegs → r ≠ .a0 → u₁.gpr r = u₂.gpr r := by
      intro r h1 h2
      have : r ∈ preserved ∨ r = .ra := by revert h1 h2; cases r <;> decide
      rcases this with hr | rfl
      · rw [ha₁.1 r hr, ha₂.1 r hr]; exact hg r h2
      · rw [ha₁.2.2, ha₂.2.2]; exact hg _ (by decide)
    refine ⟨show u₁.rd = u₂.rd by simp only [rd₁, rd₂, hrd], show u₁.wr = u₂.wr by simp only [wr₁, wr₂, hwr], fun r hr => ?_, ?_, ?_, fun x hx => ?_⟩
    · show finG _ u₁.gpr r = finG _ u₂.gpr r
      simp only [finG, hr, ite_false]
      split
      · rfl
      · next h => exact keep r h hr
    · show finG _ u₁.gpr .a0 >>> _ = finG _ u₂.gpr .a0 >>> _
      simp only [finG, show Reg.a0 ∉ scratchRegs by decide, ite_false, ite_true]
      rw [fixA_hi hrb, fixA_hi hrb]
    · show u₁.sp = u₂.sp
      rw [hsp₁, hsp₂, hsp]
    · show wipeMem (chunks stack) s₁.sp u₁.unknowns u₁.mem x = wipeMem (chunks stack) s₂.sp u₂.unknowns u₂.mem x
      rw [wipeMem_below, wipeMem_below, chunks_sum, ← hsp, hU]
      split
      · rfl
      · next hb =>
        have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
          have := hx; simp only [finState, rd₁, wr₁] at this; exact this
        have nb : ¬ (below s₁.sp c.riscv64Depth).Contains x 1 := fun h =>
          hb (below_sub hd hst x h)
        have f₁ := Exec.stackFrame a₁ hdep x (fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · exact hx' r (List.mem_append_right _ hr)
          · simp only [List.mem_singleton] at hr; subst hr; exact nb)
        have f₂ := Exec.stackFrame a₂ hdep x (fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · exact hx' r (List.mem_append_right _ (hwr ▸ hr))
          · simp only [List.mem_singleton] at hr; subst hr; rw [← hsp]; exact nb)
        rw [f₁, f₂]
        exact hm x hx'

/-! ## A registration's code, scrubbed -/

/-- The result's width, of `r`'s function. -/
abbrev retBitsOf {api : Api} (r : Unscrubbed api target) : Nat :=
  api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits

theorem contract_pub {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : A.pub s₁ s₂ := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact h.1
    | some f => exact h.1.1

/-- The functions of the tables have the same addresses in two runs that
agree on what is public. -/
theorem tables_pub_syms {A : Abi isa} {sig : Sig} {ts : List (String × List FnTable)}
    {s₁ s₂ : State} (h : (A.withTables sig ts).pub s₁ s₂) :
    ∀ f ∈ tableFns ts, s₁.syms f = s₂.syms f := by
  intro f hf
  cases ts with
  | nil => simp [tableFns] at hf
  | cons t ts => exact h.2.1 f hf

/-- `r`'s code, scrubbed, is verified against `r`'s contract and returns
without secret residue. -/
theorem scrubCode_ok {api : Api} (r : Unscrubbed api target)
    (hd : r.code.riscv64Depth ≤ r.stack) (hst : r.stack < 2 ^ 64) (h16 : r.stack % 16 = 0)
    (htc : tablesCall r.code r.tables = true)
    (hrb : retBitsOf r ≤ 64) (hpost : PostOut r.contract (retBitsOf r)) :
    Verified target (scrubAll (retBitsOf r) r.stack r.code) r.contract ∧
      NoResidue (scrubAll (retBitsOf r) r.stack r.code) r.contract (retBitsOf r) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  unfold retBitsOf at hrb hp ⊢
  rw [e] at hv hp ⊢
  have hrb' := hrb
  refine Verified.scrubAll (ScrubAbi.of r.consts api.sig r.tables) hv hd hst h16
    (fun s₁ s₂ hp n hn => tables_pub_syms (contract_pub hp) n ?_) hrb' hp
  simpa using List.all_eq_true.mp htc n hn

end Scrub

end VG.RISCV64
