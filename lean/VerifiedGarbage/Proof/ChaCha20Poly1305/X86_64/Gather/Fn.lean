module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Callee
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Loop
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the function

Untrusted: everything here is checked by Lean. With `B` the base of the
1880 bytes of stack below the stack pointer (`rsp = B + 1880`),
`vg_chacha20_poly1305_seal_gather` pushes the six argument registers in its
frame at `B + 1832` (`pushed`), puts `src` in `r11` and `dst` in `rdi`
(`entered_wp`), steps past the first slice, if there is one (`skipped_wp`:
`S0`, `L0`, the rest of the descriptors at `Rs`), gathers the other slices
after it in `dst` (`gathered_wp`, `gather_wp`), loads the call's arguments
from the frame and the stack arguments (`args_wp`) and the first slice from
its descriptor (`ready_wp`), and calls `vg_chacha20_poly1305_seal_split` on
them with `dst`, `len` and `tag` pushed at `B + 1808` (`called_wp`, by its
shared contract); the call keeps our frame and the return address above it.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather
  (Width entry next advance skipFirst gather callArgs firstArgs sealGather)
open VG.Proof.AesGcm.X86_64 (offset_nat imm_eq)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)

/-- The argument registers our frame keeps. -/
abbrev saved : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-! ## The slices after the first -/

/-- The slices `n + 1` descriptors list: the first, then those the `n`
after it list. -/
theorem listed_cons (m : Mem) (p : Addr) (n : Nat) :
    Sig.listed 64 m .u8 p (n + 1) = ⟨sb m p 0, sl m p 0⟩ :: Sig.listed 64 m .u8 (p + BitVec.ofNat 64 16) n := by
  simp only [Sig.listed, List.range_succ_eq_map, List.map_cons, List.map_map, Elem.size, Nat.mul_one,
    BitVec.setWidth_eq, Nat.zero_mul, Nat.mul_zero]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  have e : BitVec.ofNat 64 ((i + 1) * (2 * (64 / 8))) =
      BitVec.ofNat 64 16 + BitVec.ofNat 64 (i * (2 * (64 / 8))) := by
    rw [BitVec.ofNat_add_ofNat]; congr 1; omega
  simp only [Function.comp_apply, Nat.succ_eq_add_one, e, BitVec.add_assoc]

theorem gathered_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.Gcm.gathered 64 m p (n + 1) =
      bytesAt m (sb m p 0) (sl m p 0) ++ Spec.Gcm.gathered 64 m (p + BitVec.ofNat 64 16) n := by
  simp only [Spec.Gcm.gathered, listed_cons, List.flatMap_cons]; rfl

theorem gatheredLen_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.Gcm.gatheredLen 64 m p (n + 1) = sl m p 0 + Spec.Gcm.gatheredLen 64 m (p + BitVec.ofNat 64 16) n := by
  simp only [Spec.Gcm.gatheredLen, listed_cons, List.map_cons, List.sum_cons]

/-- The bytes after the first `o` of a buffer. -/
theorem drop_bytesAt (m : Mem) (q : Addr) (o n : Nat) :
    (bytesAt m q (o + n)).drop o = bytesAt m (q + BitVec.ofNat 64 o) n := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

/-! ## The blocks -/

/-- `entry`: `src` into `r11`, and `dst` (`[rsp + 56]`) into `rdi`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.gpr .rsp = P)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8) :
    WP isa (.block entry) a fun e => e.gpr .r11 = a.gpr .r8 ∧
      e.gpr .rdi = a.mem.readW (P + BitVec.ofNat 64 56) 64 ∧
      (∀ r, r ≠ .r11 → r ≠ .rdi → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [entry, hsp, r₅₆], ?_⟩
  exact ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

/-- `callArgs`: the call's arguments, from the frame and our stack arguments. -/
theorem callArgs_ok (a : State) {P : Addr} (hsp : a.gpr .rsp = P)
    (r₀ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 0) 8)
    (r₈ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 8) 8)
    (r₁₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 16) 8)
    (r₂₄ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 24) 8)
    (r₃₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 32) 8)
    (r₄₀ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 40) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8)
    (r₆₄ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 64) 8)
    (r₇₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 72) 8) :
    WP isa (.block callArgs) a fun e => e.gpr .rdi = a.mem.readW (P + BitVec.ofNat 64 40) 64 ∧
      e.gpr .rsi = a.mem.readW (P + BitVec.ofNat 64 32) 64 ∧
      e.gpr .rdx = a.mem.readW (P + BitVec.ofNat 64 24) 64 ∧
      e.gpr .rcx = a.mem.readW (P + BitVec.ofNat 64 16) 64 ∧
      e.gpr .r8 = a.mem.readW (P + BitVec.ofNat 64 8) 64 ∧
      e.gpr .r9 = a.mem.readW (P + BitVec.ofNat 64 0) 64 ∧
      e.gpr .rax = a.mem.readW (P + BitVec.ofNat 64 72) 64 ∧
      e.gpr .r10 = a.mem.readW (P + BitVec.ofNat 64 64) 64 ∧
      e.gpr .r11 = a.mem.readW (P + BitVec.ofNat 64 56) 64 ∧
      (∀ r ∈ calleeSaved, e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [callArgs, hsp, r₀, r₈, r₁₆, r₂₄, r₃₂, r₄₀, r₅₆, r₆₄, r₇₂], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

/-- The first slice's descriptor, at `r8`: its length into `r9`, then its
address into `r8`. -/
theorem firstLd_ok (a : State) {A : Addr} (h8 : a.gpr .r8 = A) (r₀ : InRegions (a.rd ++ a.wr) A 8)
    (r₈ : InRegions (a.rd ++ a.wr) (A + BitVec.ofNat 64 8) 8) :
    WP isa (.block [.mov .r9 (.mem (at_ .r8 8)), .mov .r8 (.mem (at_ .r8 0))]) a fun e =>
      e.gpr .r8 = a.mem.readW A 64 ∧ e.gpr .r9 = a.mem.readW (A + BitVec.ofNat 64 8) 64 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  have r₀' : InRegions (a.rd ++ a.wr) (A + BitVec.ofNat 64 0) 8 := by rw [BitVec.add_zero]; exact r₀
  apply WP.of_runBlock
  refine ⟨_, by xrun [h8, r₀', r₈], ?_⟩
  exact ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 1880 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.gpr .rsp - BitVec.ofNat 64 1880

/-- Our frame. -/
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 1832, 48⟩

/-- The memory after the push of our frame. -/
abbrev eM : Mem := (pushed saved s).mem

/-- Whether there is a first slice: 1, else 0. -/
abbrev k1 : Nat := if Cnt s = 0 then 0 else 1

/-- The first slice, which the call reads where it is (`src` and no bytes
without slices). -/
abbrev S0 : Addr := if Cnt s = 0 then Src s else sb (eM s) (Src s) 0
abbrev L0 : Nat := if Cnt s = 0 then 0 else sl (eM s) (Src s) 0
abbrev sR : Region := ⟨S0 s, L0 s⟩

/-- The descriptors of the other slices, and how many. -/
abbrev Rs : Addr := Src s + BitVec.ofNat 64 (16 * k1 s)
abbrev Rc : Nat := Cnt s - k1 s

/-- The other slices' bytes, and the memory once they are gathered after
the first slice's length in `dst`. -/
abbrev rest : List Byte := Spec.Gcm.gathered 64 (eM s) (Rs s) (Rc s)
abbrev gM : Mem := writeBytes (eM s) (Dst s + BitVec.ofNat 64 (L0 s)) (rest s)

/-- The regions the call of `vg_chacha20_poly1305_seal_split` reads (with
`dst`, `len` and `tag` pushed for it) and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, sR s, ⟨Bs s + BitVec.ofNat 64 1808, 24⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- The slices: the first, then the others. -/
theorem split_eM (s : State) :
    Spec.Gcm.gathered 64 (eM s) (Src s) (Cnt s) = bytesAt (eM s) (S0 s) (L0 s) ++ rest s ∧
      Spec.Gcm.gatheredLen 64 (eM s) (Src s) (Cnt s) =
        L0 s + Spec.Gcm.gatheredLen 64 (eM s) (Rs s) (Rc s) ∧
      (sR s = dsR s ∨ sR s ∈ Sig.listed 64 (eM s) .u8 (Src s) (Cnt s)) ∧
      (∀ r ∈ Sig.listed 64 (eM s) .u8 (Rs s) (Rc s), r ∈ Sig.listed 64 (eM s) .u8 (Src s) (Cnt s)) := by
  rcases Nat.eq_zero_or_eq_succ_pred (Cnt s) with h0 | h1
  · simp only [rest, sR, S0, L0, Rs, Rc, k1, dsR, h0, ite_true, Nat.zero_mul, Nat.mul_zero, Nat.sub_zero]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Spec.Gcm.gathered, Spec.Gcm.gatheredLen, Sig.listed, bytesAt]
  · have hne : Cnt s ≠ 0 := by omega
    obtain ⟨n, hn⟩ : ∃ n, Cnt s = n + 1 := ⟨_, h1⟩
    simp only [rest, sR, S0, L0, Rs, Rc, k1, hne, ite_false, Nat.mul_one]
    rw [hn, gathered_cons, gatheredLen_cons, listed_cons, Nat.add_sub_cancel]
    exact ⟨rfl, rfl, .inr List.mem_cons_self, fun r hr => List.mem_cons_of_mem _ hr⟩

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.gpr .rsp = Bs s + BitVec.ofNat 64 1880
  hBn : (Bs s).toNat + 1912 ≤ 2 ^ 64
  hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 1880

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w₁, w₂, -⟩ := id hs
  have w₁' : 1880 ≤ (s.gpr .rsp).toNat := w₁
  have w₂' : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 := w₂
  have hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 1880 := toNat_sub_ofNat w₁
  exact ⟨hs, (BitVec.sub_add_cancel _ _).symm, by omega, hBv⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 1880) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub (stkR s) :=
  Offset.sub_base _ h'

theorem covers_of_mem' {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem hP (s : State) : (pushed saved s).gpr .rsp = Bs s + BitVec.ofNat 64 1832 := by
  rw [pushed_rsp, Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1880 by decide)]; rfl

theorem hPwr (s : State) : (pushed saved s).wr = FR s :: s.wr := by
  rw [pushed_wr, Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1880 by decide)]; rfl

theorem fr_sub (s : State) : (FR s).Sub (stkR s) := stk_sub s 1832 48 (by decide)

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem w₁ : 1880 ≤ (s.gpr .rsp).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w₁, -⟩ := h.pre
  exact w₁

/-- The stack arguments. -/
theorem argAddr (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (1888 + 8 * i) := by
  show s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) = _
  rw [h.hB, Offset.add_ofNat_add_ofNat]; congr 2; omega

theorem hargR : argR s = ⟨Bs s + BitVec.ofNat 64 1888, 24⟩ := by
  show (⟨stackArgAddr s 0, 24⟩ : Region) = _
  rw [h.argAddr]

theorem pushes : Frame [FR s] s.mem (eM s) ∧
    ∀ j (hj : j < saved.length), (eM s).readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr saved[j] := by
  have := pushRegs_mem s saved (by decide) (by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega)
  rw [Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1880 by decide)] at this
  exact this

theorem frame_eM : Frame [FR s] s.mem (eM s) := h.pushes.1

/-- The words of our frame: the argument registers. -/
theorem pushedW (j : Nat) (hj : j < 6) (d : Nat) (hd : d + 8 * (j + 1) = 1880) :
    (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 = s.gpr (saved[j]'hj) := by
  have := h.pushes.2 j hj
  rw [Offset.sub_ofNat_eq _ (show 8 * (j + 1) ≤ 1880 by omega), show 1880 - 8 * (j + 1) = d by omega] at this
  exact this

/-- The memory the push left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint (stkR s)) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  h.frame_eM x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (fr_sub s x hc)

/-- The descriptors and the slices, after the push. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eM s x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds, bls, -⟩ := h.pre
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact bds.symm
  · exact (bls r hr).symm

theorem hls : Sig.listed 64 (eM s) .u8 (Src s) (Cnt s) = lsR s :=
  (Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag).1

theorem hpt : Spec.Gcm.gathered 64 (eM s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hgl : Spec.Gcm.gatheredLen 64 (eM s) (Src s) (Cnt s) = L s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgl, -⟩ := h.pre
  rw [Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl

theorem hL : L s ≤ pMax := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpm, -⟩ := h.pre
  exact hpm

/-- The first slice is the descriptors' (empty) region or one of the slices. -/
theorem sR_cases : sR s = dsR s ∨ sR s ∈ lsR s := by
  rcases (split_eM s).2.2.1 with e | e
  · exact .inl e
  · exact .inr (h.hls ▸ e)

theorem sR_d : (dR s).Disjoint (sR s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, dds, dls, -⟩ := h.pre
  rcases h.sR_cases with e | e
  · rw [e]; exact dds
  · exact dls _ e

theorem sR_t : (tgR s).Disjoint (sR s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, tds,
    tls⟩ := h.pre
  rcases h.sR_cases with e | e
  · rw [e]; exact tds
  · exact tls _ e

theorem sR_stk : (stkR s).Disjoint (sR s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds, bls, -⟩ := h.pre
  rcases h.sR_cases with e | e
  · rw [e]; exact bds
  · exact bls _ e

theorem sR_rd : sR s ∈ s.rd := by
  rw [h.pre.1]
  rcases h.sR_cases with e | e
  · rw [e]; simp
  · simp [e]

theorem sR_wrap : (S0 s).toNat + L0 s ≤ 2 ^ 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, ol, -⟩ := h.pre
  rcases h.sR_cases with e | e
  · have e₁ : S0 s = Src s := congrArg Region.base e
    have e₂ : L0 s = Cnt s * 16 := congrArg Region.len e
    rw [e₁, e₂]; exact ods
  · exact ol _ e

theorem L0_le : L0 s + (rest s).length = L s := by
  rw [Proof.Gcm.length_gathered, ← (split_eM s).2.1, h.hgl]

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  have := h.L0_le
  have hL := h.hL
  refine writeBytes_frame _ _ _ ?_
  exact Offset.contains_base _ (by omega) (by unfold pMax at hL; omega)

/-- A word of the stack, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 8 ≤ 1880) :
    (gM s).readW (Bs s + BitVec.ofNat 64 d) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact bd.sub_left (stk_sub s d 8 hd)

/-- A stack argument, once the slices are gathered. -/
theorem gArg (i : Nat) (hi : i < 3) :
    (gM s).readW (Bs s + BitVec.ofNat 64 (1888 + 8 * i)) 64 = stackArg s i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, darg, -⟩ := h.pre
  have hBn := h.hBn
  have hs : Region.Sub ⟨Bs s + BitVec.ofNat 64 (1888 + 8 * i), 8⟩ (argR s) := by
    rw [h.hargR]; exact Offset.sub _ (by omega) (by omega)
  rw [Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact darg.symm.sub_left hs) (by decide)]
  rw [Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)]
  rw [← h.argAddr]; rfl

/-- A word of the descriptors, once the slices are gathered. -/
theorem gDesc (d : Nat) (hd : d + 8 ≤ Cnt s * 16) :
    (gM s).readW (Src s + BitVec.ofNat 64 d) 64 = (eM s).readW (Src s + BitVec.ofNat 64 d) 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, dds, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, -⟩ := h.pre
  refine Frame.readW (r := dsR s) h.frame_gM (Offset.contains_base _ hd (by omega)) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact dds.symm

end Lay

/-! ## The phases -/

/-- After the push and the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  r11 : e.gpr .r11 = Src s
  rdi : e.gpr .rdi = Dst s
  gpr : ∀ r, r ≠ .r11 → r ≠ .rdi → r ≠ .rsp → e.gpr r = s.gpr r
  rsp : e.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  mx : e.mxcsr = s.mxcsr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (pushed saved s) (Entered s) := by
  have hBn := h.hBn
  have r₅₆ : InRegions ((pushed saved s).rd ++ (pushed saved s).wr)
      (Bs s + BitVec.ofNat 64 1832 + BitVec.ofNat 64 56) 8 := by
    rw [pushed_rd, Offset.add_ofNat_add_ofNat]
    refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.1]; simp), ?_⟩
    rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine WP.mono_mx (by decide +kernel) (entry_ok (pushed saved s) (hP s) r₅₆)
    fun e ⟨r11e, rdie, ge, me, rde, wre⟩ mxe => ?_
  refine ⟨me, by rw [r11e, pushed_gpr _ _ (by decide)], ?_, fun r h₁ h₂ h₃ => ?_, ?_, by rw [rde, pushed_rd],
    by rw [wre, hPwr s], by rw [mxe, pushed_mxcsr]⟩
  · rw [rdie, Offset.add_ofNat_add_ofNat, Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)]
    show _ = s.mem.readW (stackArgAddr s 0) 64
    rw [h.argAddr]
  · rw [ge r h₁ h₂, pushed_gpr _ _ h₃]
  · rw [ge _ (by decide) (by decide), hP s]

/-- Past the first slice. -/
structure Skipped (s f : State) : Prop where
  mem : f.mem = eM s
  r11 : f.gpr .r11 = Rs s
  r9 : f.gpr .r9 = BitVec.ofNat 64 (Rc s)
  rdi : f.gpr .rdi = Dst s + BitVec.ofNat 64 (L0 s)
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .rsp → f.gpr r = s.gpr r
  rsp : f.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  rd : f.rd = s.rd
  wr : f.wr = FR s :: s.wr
  mx : f.mxcsr = s.mxcsr

theorem skipped_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa skipFirst e (Skipped s) := by
  obtain ⟨rd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, -⟩ := h.pre
  have h9 : e.gpr .r9 = BitVec.ofNat 64 (Cnt s) := by
    rw [he.gpr _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have nr (r : Reg) (hr : r ∉ gatherRegs) : r ≠ .r11 ∧ r ≠ .rdi := ⟨fun e => hr (by simp [e]), fun e => hr (by simp [e])⟩
  refine WP.mono_mx (Q := fun f => f.mxcsr = s.mxcsr → Skipped s f) (by decide +kernel) ?_
    fun f hf mxf => hf (mxf.trans he.mx)
  refine WP.seq (WP.mono (cmp_ok e h9 (s.gpr .r9).isLt) fun t ⟨z, g, m, rdt, wrt⟩ => ?_)
  refine WP.ite (decide (Cnt s = 0)) (by show t.zf = _; exact z) (fun ht => ?_) (fun hf => ?_)
  · have h0 : Cnt s = 0 := by simpa using ht
    refine WP.block_nil fun hmx => ⟨by rw [m, he.mem], ?_, ?_, ?_, fun r hr hsp => ?_, by rw [g, he.rsp],
      by rw [rdt, he.rd], by rw [wrt, he.wr], hmx⟩
    · simp only [Rs, k1, h0, ite_true, Nat.mul_zero, BitVec.add_zero]; rw [g, he.r11]
    · simp only [Rc, k1, h0, ite_true, Nat.sub_zero]; rw [g, h9, h0]
    · simp only [L0, h0, ite_true]; rw [g, he.rdi]; simp
    · rw [g, he.gpr r (nr r hr).1 (nr r hr).2 hsp]
  · have h0 : Cnt s ≠ 0 := by simpa using hf
    have hBn := h.hBn
    have hin (d : Nat) (hd : d + 8 ≤ Cnt s * 16) : InRegions (t.rd ++ t.wr) (Src s + BitVec.ofNat 64 d) 8 := by
      rw [rdt, he.rd]
      exact ⟨dsR s, List.mem_append_left _ (by rw [rd]; simp), Offset.contains_base _ hd (by omega)⟩
    have r₀ : InRegions (t.rd ++ t.wr) (Src s) 8 := by
      have := hin 0 (by omega); rwa [BitVec.add_zero] at this
    refine WP.block_append (WP.mono (next_ok t (by rw [g, he.r11]) r₀ (hin 8 (by omega)))
      fun u ⟨rsiu, rcxu, r11u, gu, mu, rdu, wru⟩ => ?_)
    have hsl : u.gpr .rcx = BitVec.ofNat 64 (L0 s) := by
      simp only [L0, h0, ite_false, sl, Nat.mul_zero, BitVec.add_zero]
      rw [rcxu, m, he.mem, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.mono (advance_ok u (D := Dst s) (n := L0 s) (k := Cnt s)
      (by rw [gu _ (by decide) (by decide) (by decide), g, he.rdi]) hsl
      (by rw [gu _ (by decide) (by decide) (by decide), g, h9]) (by omega) (s.gpr .r9).isLt)
      fun f ⟨rdif, r9f, _, gf, mf, rdf, wrf⟩ hmx => ⟨by rw [mf, mu, m, he.mem], ?_, ?_, rdif, fun r hr hsp => ?_,
        ?_, by rw [rdf, rdu, rdt, he.rd], by rw [wrf, wru, wrt, he.wr], hmx⟩
    · simp only [Rs, k1, h0, ite_false, Nat.mul_one]
      rw [gf _ (by decide) (by decide), r11u]
    · simp only [Rc, k1, h0, ite_false]; exact r9f
    · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hr
      rw [gf r h₄ h₆, gu r h₃ h₂ h₈, g, he.gpr r h₈ h₄ hsp]
    · rw [gf _ (by decide) (by decide), gu _ (by decide) (by decide) (by decide), g, he.rsp]

/-- `gather`'s precondition after the first slice. -/
theorem gatherPre_of {s f : State} (h : Lay s) (hf : Skipped s f) :
    GatherPre f (Rs s) (Dst s + BitVec.ofNat 64 (L0 s)) (Rc s) (L s - L0 s) := by
  obtain ⟨rd, wr, -, -, -, -, -, -, -, dds, dls, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, -, -, -, -, -⟩ :=
    h.pre
  obtain ⟨-, hgl', -, hmem⟩ := split_eM s
  have hL0 := h.L0_le
  have hgl := h.hgl
  have hL := h.hL
  have hk : k1 s ≤ Cnt s := by simp only [k1]; split <;> omega
  have hdsub : (⟨Rs s, Rc s * 16⟩ : Region).Sub (dsR s) := Offset.sub_base _ (by simp only [Rc]; omega)
  have hdst : (⟨Dst s + BitVec.ofNat 64 (L0 s), L s - L0 s⟩ : Region).Sub (dR s) :=
    Offset.sub_base _ (by omega)
  have hRs : (Rs s).toNat + Rc s * 16 ≤ 2 ^ 64 := by
    simp only [Rs, Rc, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := Nat.mod_le ((Src s).toNat + (16 * k1 s) % 2 ^ 64) (2 ^ 64)
    have := Nat.mod_le (16 * k1 s) (2 ^ 64)
    rw [Nat.sub_mul]; omega
  exact { r11 := hf.r11
          r9 := hf.r9
          rdi := hf.rdi
          hcnt := by have := (s.gpr .r9).isLt; simp only [Rc]; omega
          dw := hRs
          lt := by unfold pMax at hL; omega
          len := by rw [hf.mem]; omega
          dsr := Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            refine ⟨dsR s, by rw [hf.rd, hf.wr, rd]; simp, 16 * k1 s, rfl, ?_⟩
            show 16 * k1 s + Rc s * 16 ≤ Cnt s * 16
            simp only [Rc]; rw [Nat.sub_mul]; omega
          lsr := fun r hr => covers_of_mem' (List.mem_append_left _ (by
            rw [hf.rd, rd, ← h.hls]; rw [hf.mem] at hr; simp [hmem r hr]))
          dw' := Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            refine ⟨dR s, by rw [hf.wr, wr]; simp, L0 s, rfl, ?_⟩
            show L0 s + (L s - L0 s) ≤ L s
            omega
          dsd := (dds.symm.sub_left hdsub).sub_right hdst
          lsd := fun r hr => by
            rw [hf.mem] at hr
            exact ((dls r (h.hls ▸ hmem r hr)).symm).sub_right hdst }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .rsp → g.gpr r = s.gpr r
  rsp : g.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr
  mx : g.mxcsr = s.mxcsr

theorem gathered_wp (w : Width) {s f : State} (h : Lay s) (hf : Skipped s f) : WP isa (gather w) f (Gathered s) := by
  refine WP.mono_mx (by cases w <;> decide +kernel) (gather_wp w f (gatherPre_of h hf)) fun g ⟨mg, kg⟩ mxg => ?_
  rw [hf.mem] at mg
  exact ⟨mg, fun r hr hsp => (kg.gpr r hr).trans (hf.gpr r hr hsp),
    (kg.gpr _ (by decide)).trans hf.rsp, kg.rd.trans hf.rd, kg.wr.trans hf.wr, mxg.trans hf.mx⟩

/-- After the call's arguments are loaded. -/
structure Args (s a : State) : Prop where
  mem : a.mem = gM s
  rdi : a.gpr .rdi = K s
  rsi : a.gpr .rsi = Nn s
  rdx : a.gpr .rdx = Ad s
  rcx : a.gpr .rcx = s.gpr .rcx
  r8 : a.gpr .r8 = Src s
  r9 : a.gpr .r9 = s.gpr .r9
  rax : a.gpr .rax = Tg s
  r10 : a.gpr .r10 = stackArg s 1
  r11 : a.gpr .r11 = Dst s
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → a.gpr r = s.gpr r
  rsp : a.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  rd : a.rd = s.rd
  wr : a.wr = FR s :: s.wr
  mx : a.mxcsr = s.mxcsr

theorem args_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgs) g (Args s) := by
  have hBn := h.hBn
  have inFr (d : Nat) (hd : d + 8 ≤ 48) :
      InRegions (g.rd ++ g.wr) (Bs s + BitVec.ofNat 64 1832 + BitVec.ofNat 64 d) 8 := by
    rw [hg.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨FR s, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains _ (by omega) (by omega) (by omega)⟩
  have inArg (d : Nat) (h₁ : 56 ≤ d) (hd : d + 8 ≤ 80) :
      InRegions (g.rd ++ g.wr) (Bs s + BitVec.ofNat 64 1832 + BitVec.ofNat 64 d) 8 := by
    rw [hg.rd, Offset.add_ofNat_add_ofNat]
    refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.1]; simp), ?_⟩
    rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine WP.mono_mx (by decide +kernel) (callArgs_ok g hg.rsp (inFr 0 (by decide)) (inFr 8 (by decide))
      (inFr 16 (by decide)) (inFr 24 (by decide)) (inFr 32 (by decide)) (inFr 40 (by decide))
      (inArg 56 (by decide) (by decide)) (inArg 64 (by decide) (by decide)) (inArg 72 (by decide) (by decide)))
    fun c ⟨rdic, rsic, rdxc, rcxc, r8c, r9c, raxc, r10c, r11c, csc, mc, rdc, wrc⟩ mxc => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd, hg.mem] at rdic rsic rdxc rcxc r8c r9c raxc r10c r11c
  have g56 := h.gArg 0 (by decide)
  have g64 := h.gArg 1 (by decide)
  have g72 := h.gArg 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at g56 g64 g72
  refine ⟨mc.trans hg.mem, ?_, ?_, ?_, ?_, ?_, ?_, raxc.trans g72, r10c.trans g64, r11c.trans g56,
    fun r hr hsp => ?_, (csc _ (by decide)).trans hg.rsp, rdc.trans hg.rd, wrc.trans hg.wr, mxc.trans hg.mx⟩
  · rw [rdic, h.gFrame 1872 (by decide)]; exact h.pushedW 0 (by decide) 1872 rfl
  · rw [rsic, h.gFrame 1864 (by decide)]; exact h.pushedW 1 (by decide) 1864 rfl
  · rw [rdxc, h.gFrame 1856 (by decide)]; exact h.pushedW 2 (by decide) 1856 rfl
  · rw [rcxc, h.gFrame 1848 (by decide)]; exact h.pushedW 3 (by decide) 1848 rfl
  · rw [r8c, h.gFrame 1840 (by decide)]; exact h.pushedW 4 (by decide) 1840 rfl
  · rw [r9c, h.gFrame 1832 (by decide)]; exact h.pushedW 5 (by decide) 1832 rfl
  · rw [csc r hr]
    refine hg.gpr r (fun hm => ?_) hsp
    simp only [calleeSaved, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr hm
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gM s
  rdi : c.gpr .rdi = K s
  rsi : c.gpr .rsi = Nn s
  rdx : c.gpr .rdx = Ad s
  rcx : c.gpr .rcx = s.gpr .rcx
  r8 : c.gpr .r8 = S0 s
  r9 : (c.gpr .r9).toNat = L0 s
  rax : c.gpr .rax = Tg s
  r10 : c.gpr .r10 = stackArg s 1
  r11 : c.gpr .r11 = Dst s
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → c.gpr r = s.gpr r
  rsp : c.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  mx : c.mxcsr = s.mxcsr

theorem ready_wp {s a : State} (h : Lay s) (ha : Args s a) : WP isa firstArgs a (Ready s) := by
  obtain ⟨rd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, -⟩ := h.pre
  have h9 : a.gpr .r9 = BitVec.ofNat 64 (Cnt s) := by rw [ha.r9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have ncs (r : Reg) (hr : r ∈ calleeSaved) : r ≠ .r8 ∧ r ≠ .r9 :=
    ⟨fun e => by subst e; simp [calleeSaved] at hr, fun e => by subst e; simp [calleeSaved] at hr⟩
  refine WP.mono_mx (Q := fun c => c.mxcsr = s.mxcsr → Ready s c) (by decide +kernel) ?_
    fun c hc mxc => hc (mxc.trans ha.mx)
  refine WP.seq (WP.mono (cmp_ok a h9 (s.gpr .r9).isLt) fun t ⟨z, g, m, rdt, wrt⟩ => ?_)
  refine WP.ite (decide (Cnt s = 0)) (by show t.zf = _; exact z) (fun ht => ?_) (fun hf => ?_)
  · have h0 : Cnt s = 0 := by simpa using ht
    refine WP.block_nil fun hmx => ⟨by rw [m, ha.mem], by rw [g, ha.rdi], by rw [g, ha.rsi], by rw [g, ha.rdx],
      by rw [g, ha.rcx], ?_, ?_, by rw [g, ha.rax], by rw [g, ha.r10], by rw [g, ha.r11],
      fun r hr hsp => by rw [g, ha.cs r hr hsp], by rw [g, ha.rsp], by rw [rdt, ha.rd], by rw [wrt, ha.wr], hmx⟩
    · simp only [S0, h0, ite_true]; rw [g, ha.r8]
    · simp only [L0, h0, ite_true]; rw [g, ha.r9]; exact h0
  · have h0 : Cnt s ≠ 0 := by simpa using hf
    have hBn := h.hBn
    have hin (d : Nat) (hd : d + 8 ≤ Cnt s * 16) : InRegions (t.rd ++ t.wr) (Src s + BitVec.ofNat 64 d) 8 := by
      rw [rdt, ha.rd]
      exact ⟨dsR s, List.mem_append_left _ (by rw [rd]; simp), Offset.contains_base _ hd (by omega)⟩
    have r₀ : InRegions (t.rd ++ t.wr) (Src s) 8 := by
      have := hin 0 (by omega); rwa [BitVec.add_zero] at this
    have d0 := h.gDesc 0 (by omega)
    have d8 := h.gDesc 8 (by omega)
    rw [BitVec.add_zero] at d0
    refine WP.mono (firstLd_ok t (by rw [g, ha.r8]) r₀ (hin 8 (by omega)))
      fun c ⟨r8c, r9c, gc, mc, rdc, wrc⟩ hmx => ⟨by rw [mc, m, ha.mem], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun r hr hsp => ?_, ?_, by rw [rdc, rdt, ha.rd], by rw [wrc, wrt, ha.wr], hmx⟩
    · rw [gc _ (by decide) (by decide), g, ha.rdi]
    · rw [gc _ (by decide) (by decide), g, ha.rsi]
    · rw [gc _ (by decide) (by decide), g, ha.rdx]
    · rw [gc _ (by decide) (by decide), g, ha.rcx]
    · simp only [S0, h0, ite_false, sb, Nat.mul_zero, BitVec.add_zero]
      rw [r8c, m, ha.mem, d0]
    · simp only [L0, h0, ite_false, sl, Nat.mul_zero, BitVec.add_zero]
      rw [r9c, m, ha.mem, d8]
    · rw [gc _ (by decide) (by decide), g, ha.rax]
    · rw [gc _ (by decide) (by decide), g, ha.r10]
    · rw [gc _ (by decide) (by decide), g, ha.r11]
    · rw [gc r (ncs r hr).1 (ncs r hr).2, g, ha.cs r hr hsp]
    · rw [gc _ (by decide) (by decide), g, ha.rsp]

/-! ## The call -/

section
variable (c : State)

/-- The state the body of the call's frame starts in: `tag`, `len` and
`dst` pushed. -/
abbrev qS : State := pushed [.rax, .r10, .r11] c

end

/-- The state the callee starts in, given the regions it reads and writes. -/
abbrev xS (s c : State) : State := (qS c).callEntry.withRegions (rdC s) (wrC s)

theorem xgpr_eq {s c : State} {r : Reg} (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]

section
variable {s c : State} (h : Lay s) (hc : Ready s c)
include h hc

omit h in
theorem Ready.qsp : (qS c).gpr .rsp = Bs s + BitVec.ofNat 64 1808 := by
  rw [pushed_rsp, hc.rsp, show 8 * [Reg.rax, Reg.r10, Reg.r11].length = 24 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]

omit h in
theorem Ready.qwr : (qS c).wr = ⟨Bs s + BitVec.ofNat 64 1808, 24⟩ :: FR s :: s.wr := by
  rw [pushed_wr, hc.rsp, hc.wr, show 8 * [Reg.rax, Reg.r10, Reg.r11].length = 24 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]

omit h in
theorem Ready.qrd : (qS c).rd = s.rd := by rw [pushed_rd, hc.rd]

theorem Ready.hn : 8 * [Reg.rax, Reg.r10, Reg.r11].length ≤ (c.gpr .rsp).toNat := by
  have := h.hBn
  rw [hc.rsp, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1832) (by decide),
    Nat.mod_eq_of_lt (by omega)]
  simp only [List.length_cons, List.length_nil]; omega

/-- The push of `tag`, `len` and `dst`. -/
theorem Ready.qmem : Frame [⟨Bs s + BitVec.ofNat 64 1808, 24⟩] c.mem (qS c).mem ∧
    (qS c).mem.readW (Bs s + BitVec.ofNat 64 1824) 64 = Tg s ∧
    (qS c).mem.readW (Bs s + BitVec.ofNat 64 1816) 64 = stackArg s 1 ∧
    (qS c).mem.readW (Bs s + BitVec.ofNat 64 1808) 64 = Dst s := by
  have := pushRegs_mem c [.rax, .r10, .r11] (by decide) (hc.hn h)
  have h₁ := this.1
  have h₂ := this.2 0 (by decide)
  have h₃ := this.2 1 (by decide)
  have h₄ := this.2 2 (by decide)
  rw [hc.rsp, show 8 * [Reg.rax, Reg.r10, Reg.r11].length = 24 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₁
  rw [hc.rsp, show 8 * (0 + 1) = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₂
  rw [hc.rsp, show 8 * (1 + 1) = 16 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₃
  rw [hc.rsp, show 8 * (2 + 1) = 24 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₄
  exact ⟨h₁, h₂.trans hc.rax, h₃.trans hc.r10, h₄.trans hc.r11⟩

omit h in
theorem Ready.xsp : (xS s c).gpr .rsp = Bs s + BitVec.ofNat 64 1800 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.qsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]

omit h in
/-- The return address of the call. -/
theorem Ready.xmem : Frame [⟨Bs s + BitVec.ofNat 64 1800, 8⟩] (qS c).mem (xS s c).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.qsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

omit h in
theorem Ready.xarg (i : Nat) : stackArgAddr (xS s c) i = Bs s + BitVec.ofNat 64 (1808 + 8 * i) := by
  show (xS s c).gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) = _
  rw [hc.xsp, Offset.add_ofNat_add_ofNat]; congr 2; omega

/-- A word the push wrote, as the callee reads it. -/
theorem Ready.xword (d : Nat) (hd : 1808 ≤ d) (hd' : d + 8 ≤ 1832) :
    (xS s c).mem.readW (Bs s + BitVec.ofNat 64 d) 64 = (qS c).mem.readW (Bs s + BitVec.ofNat 64 d) 64 := by
  have hBn := h.hBn
  exact Frame.readW (hc.xmem) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)

theorem Ready.xa0 : stackArg (xS s c) 0 = Dst s := by
  show (xS s c).mem.readW (stackArgAddr (xS s c) 0) 64 = _
  rw [hc.xarg, hc.xword h _ (by decide) (by decide)]; exact (hc.qmem h).2.2.2

theorem Ready.xa1 : stackArg (xS s c) 1 = stackArg s 1 := by
  show (xS s c).mem.readW (stackArgAddr (xS s c) 1) 64 = _
  rw [hc.xarg, hc.xword h _ (by decide) (by decide)]; exact (hc.qmem h).2.2.1

theorem Ready.xa2 : stackArg (xS s c) 2 = Tg s := by
  show (xS s c).mem.readW (stackArgAddr (xS s c) 2) 64 = _
  rw [hc.xarg, hc.xword h _ (by decide) (by decide)]; exact (hc.qmem h).2.1

/-- What the call needs. -/
theorem Ready.call : callPre (xS s c) ∧ Covers (rdC s ++ wrC s) ((qS c).rd ++ (qS c).wr) ∧
    Covers (wrC s) (qS c).wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, -, -, -, -, -, bk, bn, ba, bd, bt, -, -, ok, on, oa, od, ot,
    -⟩ := h.pre
  have hBn := h.hBn
  have hL0 : L0 s + (rest s).length = (stackArg s 1).toNat := h.L0_le
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := xgpr_eq hr
  have hstk : below (Bs s + BitVec.ofNat 64 1800) 1800 = ⟨Bs s, 1800⟩ := by
    simp only [below, add_ofNat_sub_ofNat _ (show 1800 ≤ 1800 by decide), Nat.sub_self, BitVec.add_zero]
  have hxsp : (Bs s + BitVec.ofNat 64 1800).toNat = (Bs s).toNat + 1800 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1800) (by decide),
      Nat.mod_eq_of_lt (by omega)]
  have sb (d n : Nat) (hd : d + n ≤ 1880) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
  have s0 (n : Nat) (hd : n ≤ 1880) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s, n⟩ : Region).Disjoint r := hr.sub_left (Region.sub_prefix hd)
  have bs := h.sR_stk
  have xa0 := hc.xa0 h
  have xa1 := hc.xa1 h
  have xa2 := hc.xa2 h
  have xg0 := hc.xarg 0
  simp only [Nat.mul_zero, Nat.add_zero] at xg0
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, hx .rdi (by decide), hx .rsi (by decide),
      hx .rdx (by decide), hx .rcx (by decide), hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx,
      hc.rcx, hc.r8, hc.r9, xa0, xa1, xa2, xg0, hc.xsp, hstk]
    exact ⟨by omega, by omega, trivial, trivial, kd, kt, nd, nt, ad, at_, h.sR_d.symm, h.sR_t.symm, dt,
      (sb 1808 24 (by decide) bd).symm, (sb 1808 24 (by decide) bt).symm,
      sb 1800 8 (by decide) bk, sb 1800 8 (by decide) bn, sb 1800 8 (by decide) ba, sb 1800 8 (by decide) bs,
      sb 1800 8 (by decide) bd, sb 1800 8 (by decide) bt,
      Offset.disjoint _ (.inl (by omega)) (by omega) (by omega), s0 1800 (by decide) bk, s0 1800 (by decide) bn,
      s0 1800 (by decide) ba, s0 1800 (by decide) bs, s0 1800 (by decide) bd, s0 1800 (by decide) bt,
      Offset.base_disjoint _ (by decide) (by omega), ok, on, oa, h.sR_wrap, od, ot, by omega⟩
  · refine Covers.of_mem fun r hr => ?_
    have hs : sR s ∈ (qS c).rd ++ (qS c).wr := List.mem_append_left _ (by rw [hc.qrd]; exact h.sR_rd)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    pick_goal 4
    · exact hs
    all_goals (rw [hc.qrd, hc.qwr, rd, wr]; simp)
  · rw [hc.qwr, wr]
    refine Covers.of_mem fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

end

/-- After the call, and the pop of `dst`, `len` and `tag`. -/
structure Called (s z : State) : Prop where
  out : gatherPost s z
  ret : z.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → z.gpr r = s.gpr r
  rsp : z.gpr .rsp = Bs s + BitVec.ofNat 64 1832
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  mx : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem called_wp (F : SealSplitFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.frame (.push [.rax, .r10, .r11]) (.call F.name F.code) (.pop .rax 3)) c (Called s) := by
  obtain ⟨-, -, kd, -, nd, -, ad, -, -, -, -, -, rdd, rt, bk, bn, ba, bd, -, -, -, ok, on, oa, od, -⟩ := h.pre
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  have hBn := h.hBn
  have hL := h.hL
  have hL0 : L0 s + (rest s).length = L s := h.L0_le
  have hdep := F.depth
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := xgpr_eq hr
  have hl : ((xS s c).gpr .r9).toNat ≤ (stackArg (xS s c) 1).toNat := by
    rw [hx _ (by decide), hc.r9, hc.xa1 h]; show L0 s ≤ L s; omega
  refine WP.frame (by simp) (by decide) (by decide) (hc.hn h) (WP.call_sp_mx F.verified.1 F.sp (by omega)
    (sealSplitSpec_pre hcp) hcov hw fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, _, post'⟩ mx' => ?_)
  have rsp' : s'.gpr .rsp = (qS c).gpr .rsp := cs' .rsp (by decide)
  refine ⟨rsp', wr', ?_⟩
  have hpost := sealSplitSpec_post post' hl
  simp only [hx .rdi (by decide), hx .rsi (by decide), hx .rdx (by decide), hx .rcx (by decide),
    hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx, hc.rcx, hc.r8, hc.r9, hc.xa0 h, hc.xa1 h,
    hc.xa2 h, m₂] at hpost
  -- The callee's memory on entry: ours, with `dst`, `len`, `tag` and its return address pushed below our frame.
  have fx : Frame [⟨Bs s + BitVec.ofNat 64 1808, 24⟩, ⟨Bs s + BitVec.ofNat 64 1800, 8⟩] (gM s) (xS s c).mem := by
    rw [← hc.mem]
    exact ((hc.qmem h).1.mono (fun r hr => by simp at hr ⊢; exact Or.inl hr)).trans
      ((hc.xmem).mono (fun r hr => by simp at hr ⊢; exact Or.inr hr))
  have apart {r : Region} (hr : (stkR s).Disjoint r) :
      ∀ r' ∈ [(⟨Bs s + BitVec.ofNat 64 1808, 24⟩ : Region), ⟨Bs s + BitVec.ofNat 64 1800, 8⟩], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (hr.sub_left (stk_sub s 1808 24 (by decide))).symm
    · exact (hr.sub_left (stk_sub s 1800 8 (by decide))).symm
  have hsw := h.sR_wrap
  rw [bytesAt_frame fx (apart bk) (by omega), bytesAt_frame fx (apart bn) (by omega),
    bytesAt_frame fx (apart ba) (by omega), bytesAt_frame fx (apart h.sR_stk) (by omega),
    bytesAt_frame fx (apart bd) (by omega)] at hpost
  -- The key, the nonce, the additional data and the first slice are what they were; the rest of the
  -- data is the other slices gathered.
  have hfc : Frame [FR s, dR s] s.mem (gM s) :=
    (h.frame_eM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  have apart' {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right (fr_sub s)
    · exact h₂
  rw [bytesAt_frame hfc (apart' bk kd) (by omega), bytesAt_frame hfc (apart' bn nd) (by omega),
    bytesAt_frame hfc (apart' ba ad) (by omega), bytesAt_frame hfc (apart' h.sR_stk h.sR_d.symm) (by omega)]
    at hpost
  have hd : (bytesAt (gM s) (Dst s) (L s)).drop (L0 s) = rest s := by
    rw [← hL0, drop_bytesAt]
    exact bytesAt_writeBytes_self _ _ _ (by unfold pMax at hL; omega)
  have hpt : pt s (Cnt s) = bytesAt s.mem (S0 s) (L0 s) ++ rest s := by
    rw [← h.hpt, (split_eM s).1, bytesAt_frame h.frame_eM (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sR_stk.symm.sub_right (fr_sub s)) (by omega)]
  rw [hd, ← hpt] at hpost
  refine ⟨by simp only [gatherPost, popped_mem]; exact hpost, ?_, fun r hr hsp => ?_, ?_, ?_, ?_, ?_⟩
  · -- The return address: neither the pushes, nor the copy, nor the call wrote it.
    have hsp' : (qS c).gpr .rsp = Bs s + BitVec.ofNat 64 1808 := hc.qsp
    have hbelow : below ((qS c).gpr .rsp) (F.code.x86_64Depth + 8) =
        ⟨Bs s + BitVec.ofNat 64 (1800 - F.code.x86_64Depth), F.code.x86_64Depth + 8⟩ := by
      rw [hsp']; simp only [below]
      rw [add_ofNat_sub_ofNat _ (by omega), show 1808 - (F.code.x86_64Depth + 8) = 1800 - F.code.x86_64Depth by omega]
    have e : s.gpr .rsp = Bs s + BitVec.ofNat 64 1880 := h.hB
    rw [popped_mem, e]
    have r₁ : s'.mem.readW (Bs s + BitVec.ofNat 64 1880) 64 = (qS c).mem.readW (Bs s + BitVec.ofNat 64 1880) 64 := by
      refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hbelow] at hr
      rcases hr with (rfl | rfl) | rfl
      · rw [← e]; exact rdd
      · rw [← e]; exact rt
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    have r₂ : (qS c).mem.readW (Bs s + BitVec.ofNat 64 1880) 64 = c.mem.readW (Bs s + BitVec.ofNat 64 1880) 64 :=
      Frame.readW (hc.qmem h).1 (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)
    have r₃ : (gM s).readW (Bs s + BitVec.ofNat 64 1880) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 1880) 64 :=
      Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← e]; exact rdd) (by decide)
    have r₄ : (eM s).readW (Bs s + BitVec.ofNat 64 1880) 64 = s.mem.readW (Bs s + BitVec.ofNat 64 1880) 64 :=
      Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)
    rw [r₁, r₂, hc.mem, r₃, r₄]
  · have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
    rw [popped_gpr _ _ _ hsp hra, cs' r hr, pushed_gpr _ _ hsp, hc.cs r hr hsp]
  · rw [popped_rsp, rsp', hc.qsp, Offset.add_ofNat_add_ofNat]; rfl
  · rw [popped_rd, rd', hc.qrd]
  · rw [popped_wr, wr', hc.qwr]; rfl
  · rw [popped_mxcsr, mx', pushed_mxcsr, hc.mx]

/-- The body of our frame. -/
theorem frameBody_wp (w : Width) (F : SealSplitFn) {s : State} (h : Lay s) :
    WP isa (.seq (.block entry) (.seq skipFirst (.seq (gather w) (.seq (.block callArgs) (.seq firstArgs
      (.frame (.push [.rax, .r10, .r11]) (.call F.name F.code) (.pop .rax 3)))))))
      (pushed saved s) (Called s) := by
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (skipped_wp h he) fun f hf => ?_)
  refine WP.seq (WP.mono (gathered_wp w h hf) fun g hg => ?_)
  refine WP.seq (WP.mono (args_wp h hg) fun a ha => ?_)
  refine WP.seq (WP.mono (ready_wp h ha) fun c hc => ?_)
  exact called_wp F h hc

theorem sealGather_wp (w : Width) (F : SealSplitFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather w F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  have hn : 8 * saved.length ≤ (s.gpr .rsp).toNat := by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (by simp) (by decide) (by decide) hn (WP.mono (frameBody_wp w F h) fun z hz => ?_)
  refine ⟨by rw [hz.rsp, hP s], by rw [hz.wr, hPwr s], ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp
      rw [popped_rsp, hz.rsp, Offset.add_ofNat_add_ofNat, h.hB]; rfl
    · have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hsp hra, hz.cs r hr hsp]
  · rw [popped_mem]; exact hz.ret
  · rw [popped_mxcsr]; exact hz.mx
  · have := hz.out
    simp only [gatherPost, popped_mem] at this ⊢
    exact this

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
