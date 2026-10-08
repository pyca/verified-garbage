import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Gather.Callee
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: the function

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
allocates its frame of 48 bytes at `P = esp - 48` (`WP.alloc`), keeps our
caller's `ebx`, `esi` and `edi` in it and lays out the call's seven arguments
(`entered_wp`), gathers the slices to `dst` (`gathered_wp`, AES-GCM's
gathering), calls `vg_chacha20_poly1305_seal` on them in place (`called_wp`,
by its shared contract), which keeps our frame above its arguments, and
restores the registers (`ret_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.ChaCha20Poly1305.X86.SealGather VG.WriteBytes
open VG.Impl.AesGcm.X86.SealGather (sp gather restore)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)
open VG.Proof.AesGcm.X86 (w64 w64_add toNat_w64 add_zero32 setMem gpr_setMem mem_setMem rd_setMem wr_setMem)
open VG.Proof.AesGcm.X86.Gather (GatherPre gather_wp gatherRegs allocated freed WP.alloc allocated_esp allocated_gpr
  allocated_mem allocated_rd allocated_wr)

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 88 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 88) : w64 (P + BitVec.ofNat 32 d) = w64 P + BitVec.ofNat 64 d :=
  w64_add (by omega)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 88) (he : e + 4 ≤ 88) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 =
      m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega), aP hP (by omega)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 88) (h : 4 ≤ e) :
    (m.writeW (w64 (P + BitVec.ofNat 32 e)) v).readW (w64 P) 32 = m.readW (w64 P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_zero32] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 88) (h : 4 ≤ d) :
    (m.writeW (w64 P) v).readW (w64 (P + BitVec.ofNat 32 d)) 32 = m.readW (w64 (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_zero32] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

/-- The memory after the entry, at the frame `P`: our caller's `ebx`, `esi`
and `edi` at `P + 36` … `P + 44`, and our arguments `key`, `nonce`, `aad`,
`aad_len`, `dst`, `len` and `tag` (at `P + 52` … `P + 64` and `P + 76` …
`P + 84`) at `P` … `P + 24`. -/
def eMem (m : Mem) (P : BitVec 32) (ebx esi edi : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (w64 (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
  w (w (w (w (w (w ((w (w (w m 36 ebx) 40 esi) 44 edi).writeW (w64 P) (r 52)) 4 (r 56)) 8 (r 60)) 12 (r 64))
    16 (r 76)) 20 (r 80)) 24 (r 84)

theorem entry_ok (a : State) (hP : (a.gpr .esp).toNat + 88 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 48 → InRegions a.wr (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 52 ≤ d → d + 4 ≤ 88 → InRegions (a.rd ++ a.wr) (w64 (a.gpr .esp + BitVec.ofNat 32 d)) 4) :
    WP isa (.block entry) a fun e =>
      e.mem = eMem a.mem (a.gpr .esp) (a.gpr .ebx) (a.gpr .esi) (a.gpr .edi) ∧
      e.gpr .esi = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 68)) 32 ∧
      e.gpr .ebx = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 72)) 32 ∧
      e.gpr .edx = a.mem.readW (w64 (a.gpr .esp + BitVec.ofNat 32 76)) 32 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .esi → e.gpr r = a.gpr r) ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  have hw0 : InRegions a.wr (w64 (a.gpr .esp)) 4 := by simpa only [add_zero32] using hw 0 (by decide)
  refine WP.of_runBlock ⟨_, by
    xrun [entry, sp, hw 36 (by decide), hw 40 (by decide), hw 44 (by decide), hw0, hw 4 (by decide),
      hw 8 (by decide), hw 12 (by decide), hw 16 (by decide), hw 20 (by decide), hw 24 (by decide),
      hr 52 (by decide) (by decide), hr 56 (by decide) (by decide), hr 60 (by decide) (by decide),
      hr 64 (by decide) (by decide), hr 68 (by decide) (by decide), hr 72 (by decide) (by decide),
      hr 76 (by decide) (by decide), hr 80 (by decide) (by decide), hr 84 (by decide) (by decide), add_zero32,
      rdw hP, rdw0 hP, rd0w hP], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
  · simp only [mem_setMem, mem_setReg]; rfl
  · regs []
  · regs []
  · regs []
  · simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄]
  · simp only [rd_setMem, rd_setReg]
  · simp only [wr_setMem, wr_setReg]

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 88 ≤ 2 ^ 32) (ebx esi edi : BitVec 32)
include hP

/-- The entry writes only the frame. -/
theorem eMem_frame : Frame [⟨w64 P, 48⟩] m (eMem m P ebx esi edi) := by
  have c (d : Nat) (hd : d + 4 ≤ 48) : (⟨w64 P, 48⟩ : Region).Contains (w64 (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega)]; exact Offset.contains_base _ hd (by omega)
  have c0 : (⟨w64 P, 48⟩ : Region).Contains (w64 P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨w64 P, 48⟩ : Region)
  unfold eMem; dsimp only
  refine Frame.writeW ?_ hm _ (c 24 (by decide)); refine Frame.writeW ?_ hm _ (c 20 (by decide))
  refine Frame.writeW ?_ hm _ (c 16 (by decide)); refine Frame.writeW ?_ hm _ (c 12 (by decide))
  refine Frame.writeW ?_ hm _ (c 8 (by decide)); refine Frame.writeW ?_ hm _ (c 4 (by decide))
  refine Frame.writeW ?_ hm _ c0; refine Frame.writeW ?_ hm _ (c 44 (by decide))
  refine Frame.writeW ?_ hm _ (c 40 (by decide)); refine Frame.writeW ?_ hm _ (c 36 (by decide))
  exact Frame.refl _ _

/-- The words of the frame after the entry. -/
theorem eMem_words :
    let e := eMem m P ebx esi edi
    let r (m : Mem) (d : Nat) := m.readW (w64 (P + BitVec.ofNat 32 d)) 32
    e.readW (w64 P) 32 = r m 52 ∧ r e 4 = r m 56 ∧ r e 8 = r m 60 ∧ r e 12 = r m 64 ∧ r e 16 = r m 76 ∧
      r e 20 = r m 80 ∧ r e 24 = r m 84 ∧ r e 36 = ebx ∧ r e 40 = esi ∧ r e 44 = edi := by
  simp (disch := first | decide | omega) only [eMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem sub_toNat32 {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) : (x - BitVec.ofNat 32 k).toNat = x.toNat - k := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    show 2 ^ 32 - k + x.toNat = (x.toNat - k) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem w64_sub {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    w64 (x - BitVec.ofNat 32 k) = w64 x - BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_w64, sub_toNat32 hk, BitVec.toNat_sub, toNat_w64, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by have := x.isLt; omega)]
  have := x.isLt
  rw [show 2 ^ 64 - k + x.toNat = (x.toNat - k) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The `n` bytes at `p + d` are within the `k` bytes at `p + e`. -/
theorem contains_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (hd : d - e < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  rw [show p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) by
    rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h₁]]
  exact Offset.contains_base _ (by omega) hd

/-! ## The layout -/

section
variable (s : State)

/-- The frame, the base of the 824 bytes of stack below the stack pointer,
and the frame as a region. -/
abbrev Pf : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 48
abbrev Bs : Addr := w64 (s.gpr .esp) - BitVec.ofNat 64 824
abbrev FR : Region := ⟨w64 (Pf s), 48⟩

/-- The memory after the entry. -/
abbrev eM : Mem := eMem s.mem (Pf s) (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gM : Mem := writeBytes (eM s) (w64 (Dst s)) (pt s (Cnt s))

end

/-- What `gatherPre` gives, with the frame at `Pf s` and the stack below the
stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  rd : s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s
  wr : s.wr = [dR s, tgR s, argR s]
  kd : (kR s).Disjoint (dR s)
  kt : (kR s).Disjoint (tgR s)
  nd : (nR s).Disjoint (dR s)
  nt : (nR s).Disjoint (tgR s)
  ad : (aR s).Disjoint (dR s)
  at_ : (aR s).Disjoint (tgR s)
  dt : (dR s).Disjoint (tgR s)
  dds : (dR s).Disjoint (dsR s)
  dls : ∀ r ∈ lsR s, (dR s).Disjoint r
  ed : (retR s).Disjoint (dR s)
  et : (retR s).Disjoint (tgR s)
  bk : (stkR s).Disjoint (kR s)
  bn : (stkR s).Disjoint (nR s)
  ba : (stkR s).Disjoint (aR s)
  bd : (stkR s).Disjoint (dR s)
  bt : (stkR s).Disjoint (tgR s)
  bds : (stkR s).Disjoint (dsR s)
  bls : ∀ r ∈ lsR s, (stkR s).Disjoint r
  ok : (K s).toNat + 32 ≤ 2 ^ 32
  on : (Nn s).toNat + 12 ≤ 2 ^ 32
  oa : (Ad s).toNat + AL s ≤ 2 ^ 32
  od : (Dst s).toNat + L s ≤ 2 ^ 32
  ot : (Tg s).toNat + 16 ≤ 2 ^ 32
  ods : (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32
  ol : ∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32
  w₁ : 824 ≤ (s.gpr .esp).toNat
  hgl : gl s (Cnt s) = L s
  hP : (Pf s).toNat + 88 ≤ 2 ^ 32
  hPn : (Pf s).toNat = (s.gpr .esp).toNat - 48
  hBn : (Bs s).toNat + 864 ≤ 2 ^ 32
  hA0 : w64 (Pf s) = Bs s + BitVec.ofNat 64 776
  hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 824
  sa : ∀ i, i < 9 → s.mem.readW (w64 (Pf s + BitVec.ofNat 32 (52 + 4 * i))) 32 = arg s i

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, kd, kt, -, nd, nt, -, ad, at_, -, dt, dds, dls, -, -, -, -, -, -, -, -, -, ed, et, -, -, -,
    bk, bn, ba, bd, bt, bds, bls, -, ok, on, oa, od, ot, ods, ol, w₁, w₂, hgl, -⟩ := hs
  have hPn : (Pf s).toNat = (s.gpr .esp).toNat - 48 := sub_toNat32 (by omega)
  have hB : Bs s = w64 (s.gpr .esp - BitVec.ofNat 32 824) := (w64_sub (by omega)).symm
  have hBn : (Bs s).toNat = (s.gpr .esp).toNat - 824 := by rw [hB, toNat_w64, sub_toNat32 (by omega)]
  have hE : w64 (s.gpr .esp) = Bs s + BitVec.ofNat 64 824 := (BitVec.sub_add_cancel _ _).symm
  have hA0 : w64 (Pf s) = Bs s + BitVec.ofNat 64 776 := by
    rw [w64_sub (by omega), hE, add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, ed, et, bk, bn, ba, bd, bt, bds, bls, ok, on, oa, od, ot,
    ods, ol, w₁, hgl, by omega, hPn, by omega, hA0, hE, fun i hi => ?_⟩
  show _ = s.mem.readW (w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i))) 32
  rw [show 52 + 4 * i = 48 + (4 + 4 * i) by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 824) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 824⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA {d : Nat} (hd : d < 88) : w64 (Pf s + BitVec.ofNat 32 d) = Bs s + BitVec.ofNat 64 (776 + d) := by
  rw [aP h.hP hd, h.hA0, Offset.add_ofNat_add_ofNat]

theorem fr_sub : (FR s).Sub ⟨Bs s, 824⟩ := by
  show Region.Sub ⟨w64 (Pf s), 48⟩ _; rw [h.hA0]; exact stk_sub s 776 48 (by decide)

theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 828, 36⟩ := by
  show (⟨w64 (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)), 36⟩ : Region) = _
  have := h.hPn
  have := h.hP
  rw [w64_add (by omega), h.hE, Offset.add_ofNat_add_ofNat]

theorem argIn : argR s ∈ s.wr := by rw [h.wr]; simp

/-- The words of the arguments are readable. -/
theorem inArg (d : Nat) (h₁ : 52 ≤ d) (h₂ : d + 4 ≤ 88) (rs : List Region) :
    InRegions (rs ++ s.wr) (w64 (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_append_right _ h.argIn, by
    rw [h.hArg, h.hA (by omega)]; exact contains_off _ (by omega) (by omega) (by omega)⟩

/-- The frame's words are writable. -/
theorem inFr (d : Nat) (h₂ : d + 4 ≤ 48) (rs : List Region) :
    InRegions (FR s :: rs) (w64 (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_cons_self .., by rw [aP h.hP (by omega)]; exact Offset.contains_base _ h₂ (by omega)⟩

theorem sa' (i d : Nat) (hi : i < 9) (hd : d = 52 + 4 * i) :
    s.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = arg s i := by
  subst hd; exact h.sa i hi

theorem eM_frame : Frame [FR s] s.mem (eM s) := eMem_frame h.hP _ _ _

/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 824⟩) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  h.eM_frame x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (h.fr_sub x hc)

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 32 (w64 (Src s)) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 →
    s.mem x = eM s x := by
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bls r hr).symm

theorem hpt : Spec.Gcm.gathered 32 (eM s) (w64 (Src s)) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A word of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 4 ≤ 48) :
    (gM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
  rw [h.hA (by omega)]
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact h.bd.sub_left (stk_sub s _ 4 (by omega))

end Lay

/-! ## The phases -/

theorem covers_of_mem' {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩


/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  esi : e.gpr .esi = Src s
  ebx : e.gpr .ebx = arg s 5
  edx : e.gpr .edx = Dst s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .esp → e.gpr r = s.gpr r
  esp : e.gpr .esp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 48 s) (Entered s) := by
  have ae : (allocated 48 s).gpr .esp = Pf s := allocated_esp 48 s
  refine WP.mono (entry_ok (allocated 48 s) (by rw [ae]; exact h.hP)
      (fun d hd => by rw [ae, allocated_wr]; exact h.inFr d hd _)
      (fun d h₁ h₂ => by
        rw [ae, allocated_rd, allocated_wr, show s.rd ++ FR s :: s.wr = (s.rd ++ [FR s]) ++ s.wr by simp]
        exact h.inArg d h₁ h₂ _)) fun e ⟨me, esi, ebx, edx, ge, rde, wre⟩ => ?_
  rw [ae] at me esi ebx edx
  simp only [allocated_mem] at me esi ebx edx
  rw [allocated_gpr _ _ (by decide), allocated_gpr _ _ (by decide), allocated_gpr _ _ (by decide)] at me
  refine ⟨me, esi.trans (h.sa' 4 68 (by decide) rfl), ebx.trans (h.sa' 5 72 (by decide) rfl),
    edx.trans (h.sa' 6 76 (by decide) rfl), fun r hr hsp => ?_, ?_, rde, wre⟩
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₀, h₁, -, h₃, h₄, -⟩ := hr
    rw [ge r h₀ h₁ h₃ h₄, allocated_gpr _ _ hsp]
  · rw [ge _ (by decide) (by decide) (by decide) (by decide), ae]

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { esi := he.esi
          ebx := by rw [he.ebx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          edx := he.edx
          hcnt := (arg s 5).isLt
          dw := h.ods
          fitD := h.od
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact h.hgl
          dsr := covers_of_mem' (List.mem_append_left _ (by rw [he.rd, h.rd]; simp))
          lsr := fun r hr => covers_of_mem' (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd, h.rd]; simp [hr]))
          lfit := fun r hr => h.ol r (by rw [hls] at hr; exact hr)
          dw' := covers_of_mem' (by rw [he.wr, h.wr]; simp)
          dsd := h.dds.symm
          lsd := fun r hr => (h.dls r (by rw [hls] at hr; exact hr)).symm }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .esp → g.gpr r = s.gpr r
  esp : g.gpr .esp = Pf s
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) : WP isa gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hg hsp => (kg.gpr r hg).trans (he.gpr r hg hsp),
    (kg.gpr _ (by decide)).trans he.esp, kg.rd.trans he.rd, kg.wr.trans he.wr⟩

section
variable (s : State)

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes:
its arguments are the first 28 bytes of our frame. -/
abbrev rdC : List Region := [kR s, nR s, aR s]
abbrev wrC : List Region := [dR s, tgR s, ⟨Bs s + BitVec.ofNat 64 776, 28⟩]

end

section
variable {s g : State} (h : Lay s) (hg : Gathered s g)
include h hg

theorem Gathered.espN : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 48 := by rw [hg.esp]; exact h.hPn

/-- The callee's stack pointer, below its return address. -/
theorem Gathered.cesp (rd wr : List Region) :
    w64 ((g.callEntry.withRegions rd wr).gpr .esp) = Bs s + BitVec.ofNat 64 772 := by
  have := h.w₁
  have := h.hPn
  simp only [State.withRegions_gpr, State.callEntry_esp, hg.esp]
  rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, w64_sub (by omega), h.hA0, add_ofNat_sub_ofNat _ (by decide)]

theorem Gathered.cargAddr (rd wr : List Region) :
    argAddr (g.callEntry.withRegions rd wr) 0 = Bs s + BitVec.ofNat 64 776 := by
  have e : argAddr (g.callEntry.withRegions rd wr) 0 = argAddr g.callEntry 0 := rfl
  rw [e, argAddr_callEntry, hg.esp, Nat.mul_zero, add_zero32]; exact h.hA0

/-- The callee's arguments: words of our frame. -/
theorem Gathered.args (rd wr : List Region) :
    let c := g.callEntry.withRegions rd wr
    arg c 0 = K s ∧ arg c 1 = Nn s ∧ arg c 2 = Ad s ∧ arg c 3 = arg s 3 ∧ arg c 4 = Dst s ∧ arg c 5 = arg s 7 ∧
      arg c 6 = Tg s := by
  have := h.w₁
  have := h.hP
  have := h.hPn
  have e (j : Nat) (hj : j < 7) : arg (g.callEntry.withRegions rd wr) j =
      (eM s).readW (w64 (Pf s + BitVec.ofNat 32 (4 * j))) 32 := by
    show arg g.callEntry j = _
    rw [arg_callEntry (by rw [hg.esp]; omega) (by rw [hg.esp]; omega), hg.mem, hg.esp,
      h.gFrame (4 * j) (by omega)]
  obtain ⟨w0, w4, w8, w12, w16, w20, w24, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 0 (by decide), Nat.mul_zero, add_zero32]; exact w0.trans (h.sa' 0 52 (by decide) rfl)
  · rw [e 1 (by decide)]; exact w4.trans (h.sa' 1 56 (by decide) rfl)
  · rw [e 2 (by decide)]; exact w8.trans (h.sa' 2 60 (by decide) rfl)
  · rw [e 3 (by decide)]; exact w12.trans (h.sa' 3 64 (by decide) rfl)
  · rw [e 4 (by decide)]; exact w16.trans (h.sa' 6 76 (by decide) rfl)
  · rw [e 5 (by decide)]; exact w20.trans (h.sa' 7 80 (by decide) rfl)
  · rw [e 6 (by decide)]; exact w24.trans (h.sa' 8 84 (by decide) rfl)

/-- What the call needs. -/
theorem Gathered.call :
    callPre (g.callEntry.withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (g.rd ++ g.wr) ∧
      Covers (wrC s) g.wr := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hg.args h (rdC s) (wrC s)
  have cesp := hg.cesp h (rdC s) (wrC s)
  have carg := hg.cargAddr h (rdC s) (wrC s)
  have hesp := hg.espN h
  have := h.w₁
  have := h.hP
  have := h.hBn
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, a0, a1, a2, a3, a4, a5, a6, cesp, carg,
      BitVec.add_sub_cancel]
    have espc : ((g.callEntry.withRegions (rdC s) (wrC s)).gpr .esp).toNat = (s.gpr .esp).toNat - 52 := by
      simp only [State.withRegions_gpr, State.callEntry_esp]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat32 (by omega), hesp]; omega
    have stkArg : (⟨Bs s, 772⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 776, 28⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 772) (e := 776) (k := 28) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    have retArg : (⟨Bs s + BitVec.ofNat 64 772, 4⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 776, 28⟩ :=
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    have sb (d n : Nat) (hd : d + n ≤ 824) {r : Region} (hr : (stkR s).Disjoint r) :
        (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
    refine ⟨by omega, by omega, trivial, trivial, h.kd, h.kt, (sb 776 28 (by decide) h.bk).symm, h.nd, h.nt,
      (sb 776 28 (by decide) h.bn).symm, h.ad, h.at_, (sb 776 28 (by decide) h.ba).symm, h.dt,
      (sb 776 28 (by decide) h.bd).symm, (sb 776 28 (by decide) h.bt).symm,
      sb 772 4 (by decide) h.bk, sb 772 4 (by decide) h.bn, sb 772 4 (by decide) h.ba,
      sb 772 4 (by decide) h.bd, sb 772 4 (by decide) h.bt, retArg,
      h.bk.sub_left (Region.sub_prefix (by decide)), h.bn.sub_left (Region.sub_prefix (by decide)),
      h.ba.sub_left (Region.sub_prefix (by decide)), h.bd.sub_left (Region.sub_prefix (by decide)),
      h.bt.sub_left (Region.sub_prefix (by decide)), stkArg, h.ok, h.on, h.oa, h.od, h.ot⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s]) : Covers [r] (g.rd ++ g.wr) := by
      refine covers_of_mem' (List.mem_append_left _ ?_)
      rw [hg.rd, h.rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> simp
    have hfr : Covers [⟨Bs s + BitVec.ofNat 64 776, 48⟩] (g.rd ++ g.wr) := by
      rw [← h.hA0]; exact covers_of_mem' (List.mem_append_right _ (by rw [hg.wr]; exact List.mem_cons_self ..))
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (g.rd ++ g.wr) :=
      covers_of_mem' (List.mem_append_right _ (by
        rw [hg.wr, h.wr]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
        rcases h' with rfl | rfl <;> simp))
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact inRd (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact hw' (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact hw' (by simp) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact hfr a n ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  · intro a n ⟨r, hr, hc⟩
    rw [hg.wr, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, hc⟩
    · exact ⟨_, by simp, hc⟩
    · refine ⟨FR s, List.mem_cons_self .., ?_⟩
      show Region.Contains ⟨w64 (Pf s), 48⟩ a n
      rw [h.hA0]; simp only [Region.Contains] at hc ⊢; omega

end

/-- After the call. -/
structure Called (s z : State) : Prop where
  ebx : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 36)) 32 = s.gpr .ebx
  esi : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 40)) 32 = s.gpr .esi
  edi : z.mem.readW (w64 (Pf s + BitVec.ofNat 32 44)) 32 = s.gpr .edi
  ret : z.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32
  out : encrypt (bytesAt (gM s) (w64 (K s)) 32) (bytesAt (gM s) (w64 (Nn s)) 12)
      (bytesAt (gM s) (w64 (Ad s)) (AL s)) (bytesAt (gM s) (w64 (Dst s)) (L s)) =
    (bytesAt z.mem (w64 (Dst s)) (L s), bytesAt z.mem (w64 (Tg s)) 16)
  ebp : z.gpr .ebp = s.gpr .ebp
  esp : z.gpr .esp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem called_wp (F : SealFn) {s g : State} (h : Lay s) (hg : Gathered s g) :
    WP isa (.call F.name F.code) g (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hg.call h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hg.args h (rdC s) (wrC s)
  have hdep := F.depth
  have hesp := hg.espN h
  have := h.w₁
  have := h.hBn
  have e4 : w64 (g.gpr .esp - 4) = Bs s + BitVec.ofNat 64 772 := by
    have := hg.cesp h (rdC s) (wrC s)
    simpa only [State.withRegions_gpr, State.callEntry_esp] using this
  refine WP.call F.verified.1 F.noSp (by omega) (sealSpec_pre hcp) hcov hw
    fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, _, post'⟩ => ?_
  have hpost := sealSpec_post post'
  rw [a0, a1, a2, a3, a4, a5, a6, m₂] at hpost
  -- The callee's memory on entry: ours, with its return address below our frame.
  have fc : Frame [⟨Bs s + BitVec.ofNat 64 772, 4⟩] g.mem (g.callEntry.withRegions (rdC s) (wrC s)).mem := by
    show Frame _ g.mem (g.mem.writeW (w64 (g.gpr .esp - 4)) (g.unknowns 0))
    rw [e4]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have apart {r : Region} (hr : (stkR s).Disjoint r) :
      ∀ r' ∈ [(⟨Bs s + BitVec.ofNat 64 772, 4⟩ : Region)], r.Disjoint r' := by
    intro r' hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact (hr.sub_left (stk_sub s 772 4 (by decide))).symm
  rw [bytesAt_frame fc (apart h.bk) (by omega), bytesAt_frame fc (apart h.bn) (by omega),
    bytesAt_frame fc (apart h.ba) (by have := h.oa; omega), bytesAt_frame fc (apart h.bd) (by have := h.od; omega),
    hg.mem] at hpost
  -- What the call kept: the frame above its arguments, and our return address.
  have hbelow : below (g.gpr .esp) (stackUse F.code + 4) =
      ⟨Bs s + BitVec.ofNat 64 (776 - (stackUse F.code + 4)), stackUse F.code + 4⟩ := by
    show (⟨w64 (g.gpr .esp - BitVec.ofNat 32 (stackUse F.code + 4)), _⟩ : Region) = _
    rw [w64_sub (by omega), hg.esp, h.hA0, add_ofNat_sub_ofNat _ (by omega)]
  have kept (d : Nat) (h₁ : 812 ≤ d) (h₂ : d + 4 ≤ 824 ∨ d = 824) :
      s'.mem.readW (Bs s + BitVec.ofNat 64 d) 32 = g.mem.readW (Bs s + BitVec.ofNat 64 d) 32 := by
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hbelow] at hr
    rcases hr with (rfl | rfl | rfl) | rfl
    · by_cases hd : d + 4 ≤ 824
      · exact (h.bd.sub_left (stk_sub s d 4 hd)).symm.symm
      · have e : Bs s + BitVec.ofNat 64 d = w64 (s.gpr .esp) := by
          rw [h.hE, show d = 824 by omega]
        rw [e]; exact h.ed
    · by_cases hd : d + 4 ≤ 824
      · exact (h.bt.sub_left (stk_sub s d 4 hd)).symm.symm
      · have e : Bs s + BitVec.ofNat 64 d = w64 (s.gpr .esp) := by
          rw [h.hE, show d = 824 by omega]
        rw [e]; exact h.et
    · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)
    · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  obtain ⟨-, -, -, -, -, -, -, w36, w40, w44⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi)
  have saved (d : Nat) (hd : 36 ≤ d) (hd' : d + 4 ≤ 48) :
      s'.mem.readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (w64 (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [← h.gFrame d hd', ← hg.mem, h.hA (by omega), kept _ (by omega) (.inl (by omega))]
  refine ⟨(saved 36 (by decide) (by decide)).trans w36, (saved 40 (by decide) (by decide)).trans w40,
    (saved 44 (by decide) (by decide)).trans w44, ?_, hpost, ?_, ?_, rd'.trans hg.rd, wr'.trans hg.wr⟩
  · -- The return address: neither the entry, nor the copy, nor the call wrote it.
    rw [h.hE, kept 824 (by decide) (.inr rfl), hg.mem, ← h.hE]
    rw [h.frame_gM.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ed) (by decide)]
    refine h.eM_frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint ⟨w64 (s.gpr .esp), 4⟩ ⟨w64 (Pf s), 48⟩
    rw [h.hE, h.hA0]; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by omega)
  · rw [cs' .ebp (by decide), hg.gpr .ebp (by decide) (by decide)]
  · rw [cs' .esp (by decide), hg.esp]

/-- Our caller's registers back from the frame, and the frame freed. -/
theorem ret_wp {s z : State} (h : Lay s) (hz : Called s z) :
    WP isa (.block restore) z fun z' => abiPreserved s (freed 48 z') ∧ gatherPost s (freed 48 z') := by
  have hr (d : Nat) (hd : d + 4 ≤ 48) : InRegions (z.rd ++ z.wr) (w64 (z.gpr .esp + BitVec.ofNat 32 d)) 4 := by
    rw [hz.esp, hz.wr]
    obtain ⟨r, hr, hc⟩ := h.inFr d hd s.wr
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.of_runBlock ⟨_, by xrun [restore, sp, hr 36 (by decide), hr 40 (by decide), hr 44 (by decide)], ?_⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [freed]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simp [gpr_setReg, hz.esp, hz.ebx]
    · simp [gpr_setReg, hz.esp, hz.esi]
    · simp [gpr_setReg, hz.esp, hz.edi]
    · simp [gpr_setReg, hz.ebp]
    · simp [gpr_setReg, hz.esp]; exact BitVec.sub_add_cancel _ _
  · simp only [freed, mem_setReg]; exact hz.ret
  · -- The ciphertext and the tag.
    show encrypt _ _ _ _ = (bytesAt z.mem (w64 (Dst s)) (L s), bytesAt z.mem (w64 (Tg s)) 16)
    have hfc : Frame [FR s, dR s] s.mem (gM s) :=
      (h.eM_frame.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right h.fr_sub
      · exact h₂
    have hk : bytesAt (gM s) (w64 (K s)) 32 = bytesAt s.mem (w64 (K s)) 32 :=
      bytesAt_frame hfc (apart h.bk h.kd) (by omega)
    have hn : bytesAt (gM s) (w64 (Nn s)) 12 = bytesAt s.mem (w64 (Nn s)) 12 :=
      bytesAt_frame hfc (apart h.bn h.nd) (by omega)
    have ha : bytesAt (gM s) (w64 (Ad s)) (AL s) = bytesAt s.mem (w64 (Ad s)) (AL s) :=
      bytesAt_frame hfc (apart h.ba h.ad) (by have := h.oa; omega)
    have hd : bytesAt (gM s) (w64 (Dst s)) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; have := h.od; omega)
    have := hz.out
    rw [hk, hn, ha, hd] at this
    exact this

/-- The body of the frame never writes `esp`. -/
theorem body_noSp (F : SealFn) :
    NoSp (.seq (.block entry) (.seq gather (.seq (.call F.name F.code) (.block restore))) :
      Prog isa) := by
  have he : NoSp (.block entry : Prog isa) := NoSp.of_all (by decide +kernel)
  have hg : NoSp gather := NoSp.of_all (by decide +kernel)
  have hr : NoSp (.block restore : Prog isa) := NoSp.of_all (by decide +kernel)
  intro i hi
  simp only [instrs, List.mem_append] at hi
  rcases hi with hi | hi | hi | hi
  exacts [he i hi, hg i hi, F.noSp i hi, hr i hi]

theorem sealGather_wp (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega) (body_noSp F) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (called_wp F h hg) fun z hz => ?_)
  exact ret_wp h hz

end VG.Proof.ChaCha20Poly1305.X86.Gather
