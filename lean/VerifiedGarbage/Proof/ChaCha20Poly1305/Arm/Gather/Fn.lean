import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Loop
import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Callee
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: the function

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
allocates its frame of 32 bytes at `P = sp - 32`, lays out in it the call's
stack arguments, our return address and `r0`–`r3` (`entered_wp`), gathers
the slices to `dst` (`gathered_wp`, AES-GCM's gathering), reloads `r0`–`r3`
(`ready_wp`) and calls `vg_chacha20_poly1305_seal` on them in place
(`called_wp`, by its shared contract); the call keeps our frame, so the
return address comes back from it (`ret_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Arm.RegUpd VG.Arm.FrameStack VG.Impl.ChaCha20Poly1305.Arm.SealGather VG.WriteBytes
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)
open VG.Proof.AesGcm.Arm (in_left add_ofNat_zero covers_of_mem covers_cons covers_append' covers_prefix covers_nil)
open VG.Proof.AesGcm.Arm.Gather (GatherPre gather_wp gatherRegs WP.run WP.split)

/-! ## Words of the frame -/

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 52 ≤ 2 ^ 32)
include hP

theorem aP {d : Nat} (hd : d < 52) : State.addr (P + BitVec.ofNat 32 d) = State.addr P + BitVec.ofNat 64 d :=
  addr_add (by omega)

/-- A word of the frame (or above it) after a write of another. -/
theorem rdw {d e : Nat} (v : BitVec 32) (hd : d + 4 ≤ 52) (he : e + 4 ≤ 52) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  rw [aP hP (by omega), aP hP (by omega)]
  exact Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem rdw0 {e : Nat} (v : BitVec 32) (he : e + 4 ≤ 52) (h : 4 ≤ e) :
    (m.writeW (State.addr (P + BitVec.ofNat 32 e)) v).readW (State.addr P) 32 = m.readW (State.addr P) 32 := by
  have := rdw hP (m := m) (d := 0) v (by decide) he (.inl h)
  rwa [add_ofNat_zero] at this

theorem rd0w {d : Nat} (v : BitVec 32) (hd : d + 4 ≤ 52) (h : 4 ≤ d) :
    (m.writeW (State.addr P) v).readW (State.addr (P + BitVec.ofNat 32 d)) 32 =
      m.readW (State.addr (P + BitVec.ofNat 32 d)) 32 := by
  have := rdw hP (m := m) (d := d) (e := 0) v hd (by decide) (.inr h)
  rwa [add_ofNat_zero] at this

omit hP in
theorem rds (v : BitVec 32) (a : Addr) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self m a 4 v (by decide)

end

/-- The memory after the entry, at the frame `P`: our return address and
`r0`–`r3` at `P + 12` … `P + 28`, and the three words at `P + 40`, `P + 44`
and `P + 48` (`dst`, `len`, `tag`) at `P` … `P + 8`. -/
def eMem (m : Mem) (P : BitVec 32) (lr r0 r1 r2 r3 : BitVec 32) : Mem :=
  let w (m : Mem) (d : Nat) (v : BitVec 32) := m.writeW (State.addr (P + BitVec.ofNat 32 d)) v
  let r (d : Nat) := m.readW (State.addr (P + BitVec.ofNat 32 d)) 32
  w (w ((w (w (w (w (w m 12 lr) 16 r0) 20 r1) 24 r2) 28 r3).writeW (State.addr P) (r 40)) 4 (r 44)) 8 (r 48)

theorem entry_ok (a : State) (hP : a.sp.toNat + 52 ≤ 2 ^ 32)
    (hw : ∀ d, d + 4 ≤ 32 → InRegions a.wr (State.addr (a.sp + BitVec.ofNat 32 d)) 4)
    (hr : ∀ d, 32 ≤ d → d + 4 ≤ 52 → InRegions (a.rd ++ a.wr) (State.addr (a.sp + BitVec.ofNat 32 d)) 4) :
    WP isa entry a fun e =>
      e.mem = eMem a.mem a.sp (a.gpr .lr) (a.gpr .r0) (a.gpr .r1) (a.gpr .r2) (a.gpr .r3) ∧
      e.gpr .r0 = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 32)) 32 ∧
      e.gpr .r2 = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 40)) 32 ∧
      e.gpr .lr = a.mem.readW (State.addr (a.sp + BitVec.ofNat 32 36)) 32 ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r12 → r ≠ .lr → e.gpr r = a.gpr r) ∧ e.sp = a.sp ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  have hw0 : InRegions a.wr (State.addr a.sp) 4 := by simpa only [add_ofNat_zero] using hw 0 (by decide)
  refine WP.split (l₁ := Impl.AesGcm.Arm.SealGather.setFp) (l₂ := entryWords) ?_
  refine WP.run ⟨_, by
    arun [Impl.AesGcm.Arm.SealGather.setFp, entryWords, hw 12 (by decide), hw 16 (by decide),
      hw 20 (by decide), hw 24 (by decide), hw 28 (by decide), hw0, hw 4 (by decide), hw 8 (by decide),
      hr 32 (by decide) (by decide), hr 36 (by decide) (by decide), hr 40 (by decide) (by decide),
      hr 44 (by decide) (by decide), hr 48 (by decide) (by decide), add_ofNat_zero, rdw hP, rdw0 hP, rd0w hP],
    rfl⟩ fun e he => ?_
  subst he
  exact ⟨rfl, rfl, rfl, rfl, fun r h₀ h₂ h₁₂ hl => by simp [gpr_setReg, h₀, h₂, h₁₂, hl], rfl, rfl, rfl⟩

section
variable {m : Mem} {P : BitVec 32} (hP : P.toNat + 52 ≤ 2 ^ 32) (lr r0 r1 r2 r3 : BitVec 32)
include hP

/-- The entry writes only the frame. -/
theorem eMem_frame : Frame [⟨State.addr P, 32⟩] m (eMem m P lr r0 r1 r2 r3) := by
  have c (d : Nat) (hd : d + 4 ≤ 32) : (⟨State.addr P, 32⟩ : Region).Contains (State.addr (P + BitVec.ofNat 32 d)) 4 := by
    rw [aP hP (by omega)]; exact Offset.contains_base _ hd (by omega)
  have c0 : (⟨State.addr P, 32⟩ : Region).Contains (State.addr P) 4 := by simp [Region.Contains]
  have hm := List.mem_singleton_self (⟨State.addr P, 32⟩ : Region)
  exact ((((((((Frame.refl _ m).writeW hm _ (c 12 (by decide))).writeW hm _ (c 16 (by decide))).writeW hm _
    (c 20 (by decide))).writeW hm _ (c 24 (by decide))).writeW hm _ (c 28 (by decide))).writeW hm _ c0).writeW hm _
    (c 4 (by decide))).writeW hm _ (c 8 (by decide))

/-- The words of the frame after the entry. -/
theorem eMem_words :
    let e := eMem m P lr r0 r1 r2 r3
    let r (m : Mem) (d : Nat) := m.readW (State.addr (P + BitVec.ofNat 32 d)) 32
    e.readW (State.addr P) 32 = r m 40 ∧ r e 4 = r m 44 ∧ r e 8 = r m 48 ∧ r e 12 = lr ∧ r e 16 = r0 ∧
      r e 20 = r1 ∧ r e 24 = r2 ∧ r e 28 = r3 := by
  simp (disch := first | decide | omega) only [eMem, rdw hP, rdw0 hP, rd0w hP, rds]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- The `n` bytes at `p + d` are within the `k` bytes at `p + e`. -/
theorem contains_off (p : Addr) {d n e k : Nat} (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) (hd : d - e < 2 ^ 64) :
    (⟨p + BitVec.ofNat 64 e, k⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := by
  rw [show p + BitVec.ofNat 64 d = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (d - e) by
    rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h₁]]
  exact Offset.contains_base _ (by omega) hd

/-! ## The layout -/

section
variable (s : State)

/-- The frame, the base of the 696 bytes of stack below the stack pointer,
and the frame as a region. -/
abbrev Pf : BitVec 32 := s.sp - BitVec.ofNat 32 32
abbrev Bs : Addr := State.addr s.sp - BitVec.ofNat 64 696
abbrev FR : Region := ⟨State.addr (Pf s), 32⟩

/-- The memory after the entry. -/
abbrev eM : Mem := eMem s.mem (Pf s) (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gM : Mem := writeBytes (eM s) (State.addr (Dst s)) (pt s (Cnt s))

end

/-- What `gatherPre` gives, with the frame at `Pf s` and the stack below the
stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hP : (Pf s).toNat + 52 ≤ 2 ^ 32
  hPn : (Pf s).toNat = s.sp.toNat - 32
  hBn : (Bs s).toNat + 716 ≤ 2 ^ 32
  hA0 : State.addr (Pf s) = Bs s + BitVec.ofNat 64 664
  sa : ∀ i, i < 5 → s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 (32 + 4 * i))) 32 = stackArg s i
  w₁ : 696 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w₁, w₂, hgl,
    -⟩ := id hs
  have hPn : (Pf s).toNat = s.sp.toNat - 32 := sub_toNat' (by omega)
  have hB : Bs s = State.addr (s.sp - BitVec.ofNat 32 696) := (addr_sub' (by omega)).symm
  have hBn : (Bs s).toNat = s.sp.toNat - 696 := by
    rw [hB]; simp only [State.addr, BitVec.toNat_setWidth]
    rw [sub_toNat' (by omega), Nat.mod_eq_of_lt (by omega)]
  have hA0 : State.addr (Pf s) = Bs s + BitVec.ofNat 64 664 := by
    rw [addr_sub' (by omega), show State.addr s.sp = Bs s + BitVec.ofNat 64 696 from (BitVec.sub_add_cancel _ _).symm,
      add_ofNat_sub_ofNat _ (by decide)]
  refine ⟨hs, by omega, hPn, by omega, hA0, fun i hi => ?_, w₁, hgl⟩
  show _ = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32
  rw [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 696) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 696⟩ :=
  Offset.sub_base _ h'

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem hA {d : Nat} (hd : d < 52) : State.addr (Pf s + BitVec.ofNat 32 d) = Bs s + BitVec.ofNat 64 (664 + d) := by
  rw [aP h.hP hd, h.hA0, Offset.add_ofNat_add_ofNat]

theorem fr_sub : (FR s).Sub ⟨Bs s, 696⟩ := by
  show Region.Sub ⟨State.addr (Pf s), 32⟩ _; rw [h.hA0]; exact stk_sub s 664 32 (by decide)

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

omit h in
theorem hArg : argR s = ⟨Bs s + BitVec.ofNat 64 696, 20⟩ := by
  show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 20⟩ : Region) = _
  rw [Nat.mul_zero, add_ofNat_zero, BitVec.sub_add_cancel]

/-- The words of the stack arguments are readable. -/
theorem inArg (d : Nat) (h₁ : 32 ≤ d) (h₂ : d + 4 ≤ 52) (rs : List Region) :
    InRegions (s.rd ++ rs) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_append_left _ h.argIn, by
    rw [hArg, h.hA (by omega)]; exact contains_off _ (by omega) (by omega) (by omega)⟩

/-- The frame's words are writable. -/
theorem inFr (d : Nat) (h₂ : d + 4 ≤ 32) (rs : List Region) :
    InRegions (FR s :: rs) (State.addr (Pf s + BitVec.ofNat 32 d)) 4 :=
  ⟨_, List.mem_cons_self .., by rw [aP h.hP (by omega)]; exact Offset.contains_base _ h₂ (by omega)⟩

theorem sa' (i d : Nat) (hi : i < 5) (hd : d = 32 + 4 * i) :
    s.mem.readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = stackArg s i := by
  subst hd; exact h.sa i hi

theorem eM_frame : Frame [FR s] s.mem (eM s) := eMem_frame h.hP _ _ _ _ _

/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 696⟩) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  eMem_frame h.hP _ _ _ _ _ x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (h.fr_sub x hc)

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 32 (State.addr (Src s)) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 →
    s.mem x = eM s x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds, bl, -⟩ := h.pre
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact bds.symm
  · exact (bl r hr).symm

theorem hpt : Spec.Gcm.gathered 32 (eM s) (State.addr (Src s)) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A word of the frame, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 4 ≤ 32) :
    (gM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 = (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  rw [h.hA (by omega)]
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact bd.sub_left (stk_sub s _ 4 (by omega))

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  r0 : e.gpr .r0 = Src s
  r2 : e.gpr .r2 = Dst s
  lr : e.gpr .lr = stackArg s 1
  gpr : ∀ r, r ∉ gatherRegs → e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa entry (allocated 32 s) (Entered s) := by
  refine WP.mono (entry_ok (allocated 32 s) h.hP (fun d hd => h.inFr d hd _)
      (fun d h₁ h₂ => h.inArg d h₁ h₂ _)) fun e ⟨me, r0e, r2e, lre, ge, spe, rde, wre⟩ => ?_
  refine ⟨me, r0e.trans (h.sa' 0 32 (by decide) rfl), r2e.trans (h.sa' 2 40 (by decide) rfl),
    lre.trans (h.sa' 1 36 (by decide) rfl), fun r hr => ?_, spe, rde, wre⟩
  simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h₀, -, h₂, -, h₁₂, hl⟩ := hr
  exact ge r h₀ h₂ h₁₂ hl

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { r0 := he.r0
          lr := by rw [he.lr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          r2 := he.r2
          hcnt := (stackArg s 1).isLt
          dw := ods
          fitD := od
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_of_mem (List.mem_append_left _ (by rw [he.rd]; show dsR s ∈ s.rd; rw [rd]; simp))
          lsr := fun r hr => covers_of_mem (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd]; show r ∈ s.rd; rw [rd]; simp [hr]))
          lfit := fun r hr => ol r (by rw [hls] at hr; exact hr)
          dw' := covers_of_mem (by rw [he.wr, wr]; simp)
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → g.gpr r = s.gpr r
  sp : g.sp = Pf s
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.AesGcm.Arm.SealGather.gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hg => (kg.gpr r hg).trans (he.gpr r hg), kg.sp.trans he.sp, kg.rd.trans he.rd,
    kg.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gM s
  r0 : c.gpr .r0 = s.gpr .r0
  r1 : c.gpr .r1 = s.gpr .r1
  r2 : c.gpr .r2 = s.gpr .r2
  r3 : c.gpr .r3 = s.gpr .r3
  gpr : ∀ r, r ∉ gatherRegs → c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa callArgs g (Ready s) := by
  have hr (d : Nat) (hd : d + 4 ≤ 32) : InRegions (g.rd ++ g.wr) (State.addr (g.sp + BitVec.ofNat 32 d)) 4 := by
    rw [hg.sp, hg.wr]; exact in_left (h.inFr d hd _)
  refine WP.split (l₁ := Impl.AesGcm.Arm.SealGather.setFp) (l₂ := argWords) ?_
  refine WP.run ⟨_, by
    arun [Impl.AesGcm.Arm.SealGather.setFp, argWords, add_ofNat_zero, hr 16 (by decide), hr 20 (by decide),
      hr 24 (by decide), hr 28 (by decide)], rfl⟩ fun c hc => ?_
  subst hc
  obtain ⟨-, -, -, -, w16, w20, w24, w28⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  have rd (d : Nat) (hd : d + 4 ≤ 32) : g.mem.readW (State.addr (g.sp + BitVec.ofNat 32 d)) 32 =
      (eM s).readW (State.addr (Pf s + BitVec.ofNat 32 d)) 32 := by
    rw [hg.mem, hg.sp, h.gFrame d hd]
  refine ⟨hg.mem, ?_, ?_, ?_, ?_, fun r hr => ?_, hg.sp, hg.rd, hg.wr⟩
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 16 (by decide)]; exact w16
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 20 (by decide)]; exact w20
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 24 (by decide)]; exact w24
  · simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, rd 28 (by decide)]; exact w28
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₀, h₁, h₂, h₃, h₁₂, hl⟩ := hr
    simp only [gpr_setReg, h₀, h₁, h₂, h₃, h₁₂, ↓reduceIte]
    exact hg.gpr r (by simp [gatherRegs, h₀, h₁, h₂, h₃, h₁₂, hl])

/-- The callee's stack arguments: words of our frame. -/
theorem Ready.word {s c : State} (hc : Ready s c) (rd' wr' : List Region) (i : Nat) :
    stackArg ((c.callEntry).withRegions rd' wr') i = (gM s).readW (State.addr (Pf s + BitVec.ofNat 32 (4 * i))) 32 := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, hc.mem, hc.sp]

theorem Ready.args {s c : State} (h : Lay s) (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    stackArg c' 0 = Dst s ∧ stackArg c' 1 = stackArg s 3 ∧ stackArg c' 2 = Tg s := by
  obtain ⟨w0, w4, w8, -⟩ :=
    eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
  simp only [hc.word]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.mul_zero, h.gFrame 0 (by decide), add_ofNat_zero]; exact w0.trans (h.sa' 2 40 (by decide) rfl)
  · rw [h.gFrame 4 (by decide)]; exact w4.trans (h.sa' 3 44 (by decide) rfl)
  · rw [h.gFrame 8 (by decide)]; exact w8.trans (h.sa' 4 48 (by decide) rfl)

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) (rd' wr' : List Region) :
    let c' := (c.callEntry).withRegions rd' wr'
    c'.gpr .r0 = s.gpr .r0 ∧ c'.gpr .r1 = s.gpr .r1 ∧ c'.gpr .r2 = s.gpr .r2 ∧ c'.gpr .r3 = s.gpr .r3 := by
  simp only [State.withRegions_gpr]
  exact ⟨by rw [c.callEntry_gpr (by decide), hc.r0], by rw [c.callEntry_gpr (by decide), hc.r1],
    by rw [c.callEntry_gpr (by decide), hc.r2], by rw [c.callEntry_gpr (by decide), hc.r3]⟩

section
variable (s : State)

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, ⟨Bs s + BitVec.ofNat 64 664, 12⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, -, -, -, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2⟩ := hc.args h (rdC s) (wrC s)
  have sad0 : stackArgAddr ((c.callEntry).withRegions (rdC s) (wrC s)) 0 = Bs s + BitVec.ofNat 64 664 := by
    simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, hc.sp, Nat.mul_zero, add_ofNat_zero, h.hA0]
  have hPn := h.hPn
  have hP := h.hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
      c0, c1, c2, c3, a0, a1, a2, sad0, hc.sp, h.hA0, BitVec.add_sub_cancel]
    have stkArg : (⟨Bs s, 664⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 664, 12⟩ := by
      have := Offset.disjoint (Bs s) (d := 0) (n := 664) (e := 664) (k := 12) (.inl (by decide)) (by decide)
        (by decide)
      rwa [BitVec.add_zero] at this
    refine ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, dt, (bd.sub_left (stk_sub s 664 12 (by decide))).symm,
      (bt.sub_left (stk_sub s 664 12 (by decide))).symm, bk.sub_left (Region.sub_prefix (by decide)),
      bn.sub_left (Region.sub_prefix (by decide)), ba.sub_left (Region.sub_prefix (by decide)),
      bd.sub_left (Region.sub_prefix (by decide)), bt.sub_left (Region.sub_prefix (by decide)), stkArg,
      ok, on, oa, od, ot, by omega, by omega⟩
  · have inRd {r : Region} (h' : r ∈ [kR s, nR s, aR s]) : Covers [r] (c.rd ++ c.wr) := by
      refine covers_of_mem (List.mem_append_left _ ?_)
      rw [hc.rd, rd]; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl <;> simp
    have hfr : Covers [⟨Bs s + BitVec.ofNat 64 664, 32⟩] (c.rd ++ c.wr) := by
      rw [← h.hA0]; exact covers_of_mem (List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..))
    have hw' {r : Region} (h' : r ∈ [dR s, tgR s]) : Covers [r] (c.rd ++ c.wr) :=
      covers_of_mem (List.mem_append_right _ (by rw [hc.wr, wr]; exact List.mem_cons_of_mem _ h'))
    exact covers_append' (covers_cons (inRd (r := kR s) (by simp)) (covers_cons (inRd (r := nR s) (by simp))
      (covers_cons (inRd (r := aR s) (by simp)) (covers_cons (covers_prefix hfr (by decide)) covers_nil))))
      (covers_cons (hw' (by simp)) (covers_cons (hw' (by simp)) covers_nil))
  · rw [hc.wr, wr]
    exact covers_cons (covers_of_mem (by simp)) (covers_cons (covers_of_mem (by simp)) covers_nil)

/-- After the call. -/
structure Called (s s' : State) : Prop where
  ra : s'.mem.readW (State.addr (Pf s + BitVec.ofNat 32 12)) 32 = s.gpr .lr
  out : encrypt (bytesAt (gM s) (State.addr (K s)) 32) (bytesAt (gM s) (State.addr (Nn s)) 12)
      (bytesAt (gM s) (State.addr (Ad s)) (AL s)) (bytesAt (gM s) (State.addr (Dst s)) (L s)) =
    (bytesAt s'.mem (State.addr (Dst s)) (L s), bytesAt s'.mem (State.addr (Tg s)) 16)
  gpr : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  sp : s'.sp = Pf s
  rd : s'.rd = s.rd
  wr : s'.wr = FR s :: s.wr

theorem called_wp (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call F.name F.code) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c0, c1, c2, c3⟩ := hc.callGpr (rdC s) (wrC s)
  obtain ⟨a0, a1, a2⟩ := hc.args h (rdC s) (wrC s)
  have hdep := F.depth
  have hPn := h.hPn
  have w₁ := h.w₁
  refine WP.callF (n := F.name) F.verified.1 (sealSpec_pre hcp) hcov hw (by rw [hc.sp]; omega)
    fun s' rd' wr' sp' fr' pres' post' => ?_
  have hpost := sealSpec_post post'
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2, c3, a0, a1, a2,
    hc.mem, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hpost
  -- The return address, from the frame, which the call kept.
  have ra : s'.mem.readW (State.addr (Pf s + BitVec.ofNat 32 12)) 32 = s.gpr .lr := by
    obtain ⟨-, -, -, w12, -⟩ :=
      eMem_words (m := s.mem) h.hP (s.gpr .lr) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (s.gpr .r3)
    have e : c.mem.readW (State.addr (Pf s + BitVec.ofNat 32 12)) 32 = s.gpr .lr := by
      rw [hc.mem, h.gFrame 12 (by decide)]; exact w12
    rw [← e, h.hA (by decide)]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, bt, -⟩ := h.pre
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact bd.symm.sub_right (stk_sub s _ 4 (by decide)) |>.symm
    · exact bt.symm.sub_right (stk_sub s _ 4 (by decide)) |>.symm
    · simp only [belowA, hc.sp]
      rw [addr_sub' (by omega), h.hA0, add_ofNat_sub_ofNat _ (show armStack F.code ≤ 664 by omega)]
      exact Offset.disjoint _ (.inr (by omega)) (by decide) (by have := h.hBn; omega)
  have hpres : ∀ r ∈ preserved, r ≠ .lr → r ∉ gatherRegs := by decide
  exact ⟨ra, hpost, fun r hr hl => by rw [pres' r hr hl, hc.gpr r (hpres r hr hl)],
    sp'.trans hc.sp, rd'.trans hc.rd, wr'.trans hc.wr⟩

/-- The return address back in `lr`, and the frame freed. -/
theorem ret_wp {s s' : State} (h : Lay s) (hc : Called s s') :
    WP isa Impl.ChaCha20Poly1305.Arm.SealGather.ret s' fun z => abiPreserved s (freed 32 z) ∧ gatherPost s (freed 32 z) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, -, -, -, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  have hr : InRegions (s'.rd ++ s'.wr) (State.addr (s'.sp + BitVec.ofNat 32 12)) 4 := by
    rw [hc.sp, hc.wr]; exact in_left (h.inFr 12 (by decide) _)
  refine WP.split (l₁ := Impl.AesGcm.Arm.SealGather.setFp) (l₂ := [Instr.ldr .lr .r12 12]) ?_
  refine WP.run ⟨_, by arun [Impl.AesGcm.Arm.SealGather.setFp, add_ofNat_zero, hr], rfl⟩ fun z hz => ?_
  subst hz
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · -- The callee-saved registers.
    have h12 : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    simp only [freed, gpr_setReg, h12, ↓reduceIte]
    by_cases hl : r = .lr
    · subst hl; simp only [↓reduceIte]; rw [hc.sp]; exact hc.ra
    · simp only [hl, ↓reduceIte]; exact hc.gpr r hr hl
  · -- The stack pointer.
    simp only [freed, sp_setReg, hc.sp]
    exact BitVec.sub_add_cancel _ _
  · -- The ciphertext and the tag.
    show encrypt _ _ _ _ = (bytesAt s'.mem (State.addr (Dst s)) (L s), bytesAt s'.mem (State.addr (Tg s)) 16)
    have hfc : Frame [FR s, dR s] s.mem (gM s) :=
      (h.eM_frame.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 696⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right h.fr_sub
      · exact h₂
    have hk : bytesAt (gM s) (State.addr (K s)) 32 = bytesAt s.mem (State.addr (K s)) 32 :=
      bytesAt_frame hfc (apart bk kd) (by omega)
    have hn : bytesAt (gM s) (State.addr (Nn s)) 12 = bytesAt s.mem (State.addr (Nn s)) 12 :=
      bytesAt_frame hfc (apart bn nd) (by omega)
    have ha : bytesAt (gM s) (State.addr (Ad s)) (AL s) = bytesAt s.mem (State.addr (Ad s)) (AL s) :=
      bytesAt_frame hfc (apart ba ad) (by omega)
    have hd : bytesAt (gM s) (State.addr (Dst s)) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; omega)
    have := hc.out
    rw [hk, hn, ha, hd] at this
    exact this

theorem sealGather_wp (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  have w₁ := h.w₁
  refine WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by omega) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp F h hc) fun s' hs' => ?_)
  exact ret_wp h hs'

end VG.Proof.ChaCha20Poly1305.Arm.Gather
