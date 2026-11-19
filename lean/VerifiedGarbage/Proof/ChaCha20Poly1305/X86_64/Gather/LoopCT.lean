module

import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
meta import VerifiedGarbage.Spec.Gcm.OutOfPlace
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-! ### `ChaCha20Poly1305.X86_64.Gather.Loop`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: gathering the slices

Untrusted: everything here is checked by Lean. `gather` copies the `cnt`
slices that the descriptors at `r11` list, one after the other, to `rdi`
(`gather_wp`): with `i` of them copied (`GInv`), `r11` is at descriptor `i`,
`r9` holds `cnt - i`, `rdi` is `gatheredLen` of the first `i` past `dst`,
and the memory is the one on entry with their concatenation (`gathered`)
written at `dst`. The descriptors and the slices are apart from `dst`, so
they are what they were on entry. Descriptor `i` is at `Src + 16i`: the
slice's address (`sb`), then its length (`sl`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width copyBytes next advance gatherLoop gather)
open VG.Proof.AesGcm.X86_64 (ofNat_add_ofNat ofNat_sub sub_beq length_bytesAt bytesAt_frame imm_eq offset_nat)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.rax, .rcx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- What the gathering keeps: the other registers and the permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

section
variable (m : Mem) (Src : Addr)

/-- Slice `i`: its address and its length. -/
abbrev sb (i : Nat) : Addr := m.readW (Src + BitVec.ofNat 64 (16 * i)) 64
abbrev sl (i : Nat) : Nat := (m.readW (Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8) 64).toNat

end

theorem desc_off (i : Nat) : i * (2 * (64 / 8)) = 16 * i := by omega_using []

theorem gl_succ (m : Mem) (Src : Addr) (i : Nat) :
    gatheredLen 64 m Src (i + 1) = gatheredLen 64 m Src i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, desc_off]

theorem pt_succ (m : Mem) (Src : Addr) (i : Nat) :
    gathered 64 m Src (i + 1) = gathered 64 m Src i ++ bytesAt m (sb m Src i) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, desc_off, BitVec.setWidth_eq]

theorem gl_mono (m : Mem) (Src : Addr) {i j : Nat} (h : i ≤ j) :
    gatheredLen 64 m Src i ≤ gatheredLen 64 m Src j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ]; exact Nat.le_trans (ih (by omega_using [h])) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) (Src : Addr) {i cnt : Nat} (hi : i < cnt) :
    (⟨sb m Src i, sl m Src i⟩ : Region) ∈ Sig.listed 64 m .u8 Src cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  simp only [desc_off, BitVec.setWidth_eq, Elem.size, Nat.mul_one]

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : Addr) (cnt L : Nat) : Prop where
  r11 : t.gpr .r11 = Src
  r9 : t.gpr .r9 = BitVec.ofNat 64 cnt
  rdi : t.gpr .rdi = Dst
  hcnt : cnt < 2 ^ 64
  dw : Src.toNat + cnt * 16 ≤ 2 ^ 64
  lt : L < 2 ^ 63
  len : gatheredLen 64 t.mem Src cnt = L
  dsr : Covers [⟨Src, cnt * 16⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, Covers [r] (t.rd ++ t.wr)
  dw' : Covers [⟨Dst, L⟩] t.wr
  dsd : (⟨Src, cnt * 16⟩ : Region).Disjoint ⟨Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 64 t.mem .u8 Src cnt, r.Disjoint ⟨Dst, L⟩

/-- `GatherPre`, in a state with the same registers, memory and permissions. -/
theorem GatherPre.of_eq {t t' : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    GatherPre t' Src Dst cnt L :=
  { h with r11 := by rw [hg, h.r11], r9 := by rw [hg, h.r9], rdi := by rw [hg, h.rdi],
           len := by rw [hm, h.len], dsr := by rw [hrd, hwr]; exact h.dsr,
           lsr := by rw [hrd, hwr, hm]; exact h.lsr, dw' := by rw [hwr]; exact h.dw',
           lsd := by rw [hm]; exact h.lsd }

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  r11 : u.gpr .r11 = Src + BitVec.ofNat 64 (16 * i)
  r9 : u.gpr .r9 = BitVec.ofNat 64 (cnt - i)
  rdi : u.gpr .rdi = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

/-- After `next`: descriptor `i` loaded. -/
structure NInv (t u : State) (Src Dst : Addr) (cnt i : Nat) : Prop where
  r11 : u.gpr .r11 = Src + BitVec.ofNat 64 (16 * (i + 1))
  r9 : u.gpr .r9 = BitVec.ofNat 64 (cnt - i)
  rdi : u.gpr .rdi = Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)
  rsi : u.gpr .rsi = sb t.mem Src i
  rcx : u.gpr .rcx = BitVec.ofNat 64 (sl t.mem Src i)
  mem : u.mem = writeBytes t.mem Dst (gathered 64 t.mem Src i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.r11]; simp, by rw [h.r9, Nat.sub_zero], by rw [h.rdi]; simp [gatheredLen, Sig.listed],
    by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩

theorem next_ok (u : State) {A : Addr} (h11 : u.gpr .r11 = A) (r₁ : InRegions (u.rd ++ u.wr) A 8)
    (r₂ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 8) 8) :
    WP isa (.block next) u fun u' => u'.gpr .rsi = u.mem.readW A 64 ∧
      u'.gpr .rcx = u.mem.readW (A + BitVec.ofNat 64 8) 64 ∧ u'.gpr .r11 = A + BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .r11 → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧
      u'.rd = u.rd ∧ u'.wr = u.wr := by
  have r₀ : InRegions (u.rd ++ u.wr) (A + BitVec.ofNat 64 0) 8 := by rw [BitVec.add_zero]; exact r₁
  have i16 := imm_eq (n := 16) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [next, h11, r₀, r₂, i16], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg, gpr_arithFlags],
    fun r a b c => by simp [gpr_setReg, gpr_arithFlags, a, b, c], by simp [mem_setReg, mem_arithFlags],
    by simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags]⟩

theorem ofNat_beq_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a == 0) = decide (a = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  rfl

theorem advance_ok (u : State) {D : Addr} {n k : Nat} (hdi : u.gpr .rdi = D) (hcx : u.gpr .rcx = BitVec.ofNat 64 n)
    (h9 : u.gpr .r9 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    WP isa (.block advance) u fun u' => u'.gpr .rdi = D + BitVec.ofNat 64 n ∧
      u'.gpr .r9 = BitVec.ofNat 64 (k - 1) ∧ u'.zf = some (decide (k - 1 = 0)) ∧
      (∀ r, r ≠ .rdi → r ≠ .r9 → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have i1 := imm_eq (n := 1) (by decide)
  have e : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := ofNat_sub hk hk'
  apply WP.of_runBlock
  refine ⟨_, by xrun [advance, hdi, hcx, h9, i1, e], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_arithFlags], by simp [gpr_setReg, gpr_arithFlags], ?_,
    fun r a b => by simp [gpr_setReg, gpr_arithFlags, a, b], by simp [mem_setReg, mem_arithFlags],
    by simp [rd_setReg, rd_arithFlags], by simp [wr_setReg, wr_arithFlags]⟩
  simp only [zf_setReg, zf_arithFlags]
  rw [ofNat_beq_zero (by omega_using [hk'])]

section
variable {t u : State} {Src Dst : Addr} {cnt L i : Nat} (w : Width) (h : GatherPre t Src Dst cnt L)
include h

omit h in
/-- What the loop has written is within `dst`. -/
theorem frame_of {xs : List Byte} (hm : u.mem = writeBytes t.mem Dst xs) (hx : xs.length ≤ L) :
    Frame [⟨Dst, L⟩] t.mem u.mem := by
  rw [hm]
  refine writeBytes_frame t.mem Dst _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]
  omega_using [hx]

theorem gl_le (hi : i ≤ cnt) : gatheredLen 64 t.mem Src i ≤ L := h.len ▸ gl_mono t.mem Src hi

theorem len_le (hi : i ≤ cnt) : (gathered 64 t.mem Src i).length ≤ L :=
  (Proof.Gcm.length_gathered _ _ _ _) ▸ gl_le h hi

/-- The descriptors are what they were. -/
theorem desc_of (hf : Frame [⟨Dst, L⟩] t.mem u.mem) (d : Nat) (hd : d + 8 ≤ cnt * 16) :
    u.mem.readW (Src + BitVec.ofNat 64 d) 64 = t.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨Src, cnt * 16⟩) (Offset.contains_base Src hd (by have := h.dw; omega_using [hd, this]))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.dsd) (by decide)

theorem next_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.block next) u (NInv t · Src Dst cnt i) := by
  have hdw := h.dw
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hin (d : Nat) (hd : d + 8 ≤ cnt * 16) : InRegions (u.rd ++ u.wr) (Src + BitVec.ofNat 64 d) 8 := by
    rw [hu.keep.rd, hu.keep.wr]; exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base Src hd (by omega_using [hdw, hd])⟩
  have ha8 : Src + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8 = Src + BitVec.ofNat 64 (16 * i + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine WP.mono (next_ok u hu.r11 (hin _ (by omega_using [hi])) (by rw [ha8]; exact hin _ (by omega_using [hi])))
    fun u₁ ⟨rsi₁, rcx₁, r11₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [desc_of h hfr _ (by omega_using [hi])] at rsi₁
  rw [ha8, desc_of h hfr _ (by omega_using [hi]), ← ha8] at rcx₁
  exact ⟨by rw [r11₁, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ],
    by rw [g₁ _ (by decide) (by decide) (by decide), hu.r9], by rw [g₁ _ (by decide) (by decide) (by decide), hu.rdi],
    rsi₁, by rw [rcx₁, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [m₁, hu.mem],
    hu.keep.trans ⟨fun r hr => g₁ r (by intro e; subst e; simp [gatherRegs] at hr)
      (by intro e; subst e; simp [gatherRegs] at hr) (by intro e; subst e; simp [gatherRegs] at hr), rd₁, wr₁⟩⟩

/-- What the copy of slice `i` needs, after `next`. -/
theorem copyPre_of (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    CopyPre u (sb t.mem Src i) (Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i)) (sl t.mem Src i) := by
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega_using [hi])
  rw [gl_succ] at hgl
  have hmem := slice_mem t.mem Src hi
  have hsub : (⟨Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i), sl t.mem Src i⟩ : Region).Sub ⟨Dst, L⟩ :=
    Offset.sub_base _ hgl
  exact ⟨hu.rsi, hu.rdi, hu.rcx, by omega_using [hL, hgl], by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem,
    by rw [hu.keep.wr]; exact Proof.AesGcm.X86_64.covers_off h.dw' hgl (by omega_using [hL]), (h.lsd _ hmem).sub_right hsub⟩

theorem rest_wp (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    WP isa (.seq (copyBytes w) (.block advance)) u fun u' =>
      GInv t u' Src Dst cnt (i + 1) ∧ u'.zf = some (decide (i + 1 = cnt)) := by
  have hc := h.hcnt
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega_using [hi])
  have hlen : (gathered 64 t.mem Src i).length = gatheredLen 64 t.mem Src i := Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ] at hgl
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hsd : (⟨sb t.mem Src i, sl t.mem Src i⟩ : Region).Disjoint ⟨Dst, L⟩ := h.lsd _ (slice_mem t.mem Src hi)
  have hcp := copyPre_of h hi hu
  refine WP.seq (WP.mono (copyBytes_ok hcp w) fun u₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (advance_ok u₂ (D := Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i))
    (n := sl t.mem Src i) (k := cnt - i)
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.rdi])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.rcx])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.r9]) (by omega_using [hi]) (by omega_using [hc]))
    fun u₃ ⟨rdi₃, r9₃, zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (sb t.mem Src i) (sl t.mem Src i) = bytesAt t.mem (sb t.mem Src i) (sl t.mem Src i) := by
    refine bytesAt_frame hfr (fun r hr => ?_) (by omega_using [hL, hgl])
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨⟨?_, ?_, ?_, ?_, hu.keep.trans ⟨fun r hr => ?_, rd₃.trans rd₂, wr₃.trans wr₂⟩⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide), hu.r11]
  · rw [r9₃, Nat.sub_sub]
  · rw [rdi₃, BitVec.add_assoc, ← BitVec.ofNat_add, ← gl_succ]
  · rw [m₃, m₂, hbytes, hu.mem, pt_succ, ← hlen,
      writeBytes_append _ _ _ _ (by rw [hlen, length_bytesAt]; omega_using [hL, hgl])]
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hr
    rw [g₃ r h₄ h₆, g₂ r h₁ h₅ h₇]
  · rw [zf₃]; congr 1; simp only [decide_eq_decide]; omega_using [hi]

/-- One iteration of the loop. -/
theorem body_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.seq (.block next) (.seq (copyBytes w) (.block advance))) u fun u' =>
      GInv t u' Src Dst cnt (i + 1) ∧ u'.zf = some (decide (i + 1 = cnt)) :=
  WP.seq (WP.mono (next_wp h hi hu) fun _ h₁ => rest_wp w h hi h₁)

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (w : Width) (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa (gatherLoop w) t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  have hc := h.hcnt
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.mono (body_wp w h hi hu) fun u₃ ⟨h₃, z₃⟩ => ?_
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = cnt) := by show u₃.zf.map (!·) = _; rw [z₃]; rfl
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], h₃⟩

/-- The test of `src_count`. -/
theorem cmp_ok (t : State) {cnt : Nat} (h9 : t.gpr .r9 = BitVec.ofNat 64 cnt) (hc : cnt < 2 ^ 64) :
    WP isa (.block [.alu .cmp .r9 (imm 0)]) t fun t' => t'.zf = some (decide (cnt = 0)) ∧
      t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have i0 := imm_eq (n := 0) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [h9, i0], ?_⟩
  refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl⟩
  simp only [zf_arithFlags]
  show some (BitVec.ofNat 64 cnt - BitVec.ofNat 64 0 == 0) = _
  rw [Offset.ofNat_sub_ofNat_beq hc (by decide)]

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (w : Width) (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa (gather w) t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  refine WP.seq (WP.mono (cmp_ok t h.r9 h.hcnt) fun t₁ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have h' : GatherPre t₁ Src Dst cnt L := h.of_eq g₁ m₁ rd₁ wr₁
  have kp : GKeeps t t₁ := ⟨fun r _ => by rw [g₁], rd₁, wr₁⟩
  refine WP.ite (decide (cnt = 0)) (by show t₁.zf = _; exact z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by rw [m₁]; simp [gathered, Sig.listed, writeBytes_nil], kp⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    refine WP.mono (gatherLoop_wp w t₁ h' (by omega_using [h0])) fun t' ⟨m', k'⟩ => ⟨?_, kp.trans k'⟩
    rw [m', m₁]

/-! ## What the code before the call keeps -/

theorem execBlock_unknowns_eq : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.unknowns = s.unknowns
  | [], _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_unknowns_eq h₂).trans (RTaint.exec_unknowns e)

/-- Code of blocks, branches and loops only, with no call, frame or indirect
call: its runs keep the unknowns (`Exec.unknowns_of_flat`), as the code
before `seal_gather`'s call is. -/
def flatCode : Prog isa → Bool
  | .block _ => true
  | .seq a b => flatCode a && flatCode b
  | .ite _ a b => flatCode a && flatCode b
  | .loop b _ => flatCode b
  | _ => false

theorem Exec.unknowns_of_flat {c : Prog isa} {s u : State} {t : List Leak} (he : Exec isa c s t u) :
    flatCode c = true → u.unknowns = s.unknowns := by
  induction he with
  | block h => exact fun _ => execBlock_unknowns_eq h
  | seq _ _ ih₁ ih₂ =>
    intro hc; simp only [flatCode, Bool.and_eq_true] at hc; rw [ih₂ hc.2, ih₁ hc.1]
  | iteT _ _ ih => intro hc; simp only [flatCode, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [flatCode, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => intro hc; rw [ih₂ hc, ih₁ hc]
  | call => intro hc; cases hc
  | frame => intro hc; cases hc
  | icall => intro hc; cases hc
  | icallNext => intro hc; cases hc

/-- `Q` of the state after flat code, which may assume it has the unknowns
and the addresses of statics it had before. -/
theorem WP.mono_flat {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (hc : flatCode c = true) (k : ∀ u, Q u → u.unknowns = s.unknowns → u.syms = s.syms → R u) :
    WP isa c s R := by
  obtain ⟨t, u, he, hq⟩ := h
  exact ⟨t, u, he, k u hq (Exec.unknowns_of_flat he hc) (Exec.syms he)⟩

theorem gather_flat (w : Width) : flatCode (gather w) = true := by cases w <;> rfl

theorem pushed_unknowns (rs : List Reg) (s : State) : (pushed rs s).unknowns = s.unknowns := by
  show (pushRegs s rs).unknowns = s.unknowns
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans rfl

theorem pushed_syms (rs : List Reg) (s : State) : (pushed rs s).syms = s.syms := pushRegs_syms s rs

end VG.Proof.ChaCha20Poly1305.X86_64.Gather

end

end

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: gathering in constant time

Untrusted: everything here is checked by Lean. Runs are related piece by
piece from given states (`Eq2`), as on x86 (`Proof/AesGcm/X86/Gather/LoopCT.lean`).
Two runs of `gather` whose descriptors agree, from states the correctness
proof describes with the same arguments (`GatherPre`), leak the same trace
(`gather_rel`): the gathering loads the descriptors from where they are
(`r11`), and copies each slice from and to the addresses they give
(`rsi`, `rdi`), with branches on the number of slices and their lengths
(`rcx`, `r9`), registers the correctness proof pins to the same values in
both runs, from which the taint analysis checks each block.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width copyBytes next advance gatherLoop gather)
open VG.Proof.AesGcm.X86_64 (rel_taint)
open VG.Spec.Gcm (gathered gatheredLen)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_regs {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT :=
  rel_taint rs (fun _ _ hab => by obtain ⟨rfl, rfl⟩ := hab; exact hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT := by
  intro x y t₁ t₂ x' y' _ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, trivial⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The descriptors -/

/-- The descriptors agree in two memories: so do the slices they list. -/
theorem desc_agree {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
    (hd : ∀ j < cnt * 16, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j)) {i : Nat} (hi : i ≤ cnt) :
    ∀ a, (Sig.descRegion 64 Src i).Contains a 1 → m₁ a = m₂ a := by
  intro a ha
  simp only [Sig.descRegion, Region.Contains] at ha
  have e : Src + BitVec.ofNat 64 (a - Src).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← e]
  exact hd _ (by have := Nat.mul_le_mul_right 16 hi; simp only [show 2 * (64 / 8) = 16 from rfl] at ha; omega_using [hi, ha])

section
variable {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
  (hd : ∀ j < cnt * 16, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j))
include hd

theorem gl_agree {i : Nat} (hi : i ≤ cnt) : gatheredLen 64 m₁ Src i = gatheredLen 64 m₂ Src i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 64 .u8 Src i (desc_agree hd hi)]

theorem desc_word {d : Nat} (h : d + 8 ≤ cnt * 16) :
    m₁.readW (Src + BitVec.ofNat 64 d) 64 = m₂.readW (Src + BitVec.ofNat 64 d) 64 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega_using [h, hk])

theorem sb_agree {i : Nat} (hi : i < cnt) : sb m₁ Src i = sb m₂ Src i :=
  desc_word hd (by omega_using [hi])

theorem sl_agree {i : Nat} (hi : i < cnt) : sl m₁ Src i = sl m₂ Src i := by
  simp only [sl]
  rw [Offset.add_ofNat_add_ofNat, desc_word hd (by omega_using [hi])]

end

/-! ## Gathering -/

section
variable (w : Width) {t₁ t₂ : State} {Src Dst : Addr} {cnt L : Nat}
  (hd : ∀ j < cnt * 16, t₁.mem (Src + BitVec.ofNat 64 j) = t₂.mem (Src + BitVec.ofNat 64 j))
  (h₁ : GatherPre t₁ Src Dst cnt L) (h₂ : GatherPre t₂ Src Dst cnt L)
include hd h₁ h₂

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq (copyBytes w) (.block advance)))
      (fun u₁ u₂ => (GInv t₁ u₁ Src Dst cnt (i + 1) ∧ u₁.zf = some (decide (i + 1 = cnt))) ∧
        (GInv t₂ u₂ Src Dst cnt (i + 1) ∧ u₂.zf = some (decide (i + 1 = cnt)))) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq (copyBytes w) (.block advance))) TT := by
    intro σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨g₁, g₂⟩ e₁ e₂
    refine rel_seq (rel_regs [.r11] (by simp [g₁.r11, g₂.r11]) ⟨_, by taint_decide⟩)
      (next_wp h₁ hi g₁) (next_wp h₂ hi g₂) (fun τ₁ τ₂ n₁ n₂ => ?_) σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨rfl, rfl⟩ e₁ e₂
    have p₁ := copyPre_of h₁ hi n₁
    have p₂ := copyPre_of h₂ hi n₂
    rw [← sb_agree hd hi, ← sl_agree hd hi, ← gl_agree hd (Nat.le_of_lt hi)] at p₂
    refine rel_seq (rel_regs [.rsi, .rdi, .rcx] (by simp [p₁.rsi, p₂.rsi, p₁.rdi, p₂.rdi, p₁.rcx, p₂.rcx])
      (by cases w <;> exact ⟨_, by taint_decide⟩)) (copyBytes_ok p₁ w) (copyBytes_ok p₂ w) fun v₁ v₂ c₁ c₂ => ?_
    refine rel_regs [.rdi, .rcx, .r9] ?_ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨by rw [c₁.2.1 _ (by decide) (by decide) (by decide), c₂.2.1 _ (by decide) (by decide) (by decide),
        p₁.rdi, p₂.rdi], by rw [c₁.2.1 _ (by decide) (by decide) (by decide),
        c₂.2.1 _ (by decide) (by decide) (by decide), p₁.rcx, p₂.rcx], ?_⟩
    rw [c₁.2.1 _ (by decide) (by decide) (by decide), c₂.2.1 _ (by decide) (by decide) (by decide), n₁.r9, n₂.r9]
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ => ⟨body_wp w h₁ hi g₁, body_wp w h₂ hi g₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- `gatherLoop`, in two runs. -/
theorem gatherLoop_rel (hpos : cnt ≠ 0) : RelCT isa (Eq2 t₁ t₂) (gatherLoop w) TT := by
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega_using [hpos], GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel w hd h₁ h₂ hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩
    have ev₁ : isa.eval .ne u₁ = some !decide (i + 1 = cnt) := by show u₁.zf.map (!·) = _; rw [z₁]; rfl
    have ev₂ : isa.eval .ne u₂ = some !decide (i + 1 = cnt) := by show u₂.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega_using [hi, ht]
    exact ⟨cnt - (i + 1), by omega_using [hi], i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

/-- `gather`, in two runs. -/
theorem gather_rel : RelCT isa (Eq2 t₁ t₂) (gather w) TT := by
  refine rel_seq (rel_regs [.r9] (by simp [h₁.r9, h₂.r9]) ⟨_, by taint_decide⟩)
    (cmp_ok t₁ h₁.r9 h₁.hcnt) (cmp_ok t₂ h₂.r9 h₂.hcnt) fun τ₁ τ₂ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine rel_ite (b := decide (cnt = 0)) z₁ z₂ (fun _ => rel_skip) fun hf => ?_
  exact gatherLoop_rel w (by rw [m₁, m₂]; exact hd) (h₁.of_eq g₁ m₁ rd₁ wr₁) (h₂.of_eq g₂ m₂ rd₂ wr₂)
    (by simpa using hf)

end

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
