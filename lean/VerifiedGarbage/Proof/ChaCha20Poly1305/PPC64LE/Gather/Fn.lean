module

public import VerifiedGarbage.Proof.Gather.PPC64LE.Loop
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, PPC64LE: the function

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
allocates its frame of 80 bytes at `Pf = Bs + 848`, with `Bs` the base of the
928 bytes of stack below the stack pointer (`sp = Bs + 928`); keeps `key`,
`nonce`, `aad`, `aad_len`, `dst` and our return address in the six
doublewords at `Pf + 32` (`slot`), `len` in `r10` and `tag`, from `Pf + 176`,
in `r11` (`entered_wp`); gathers the slices to `dst` (`gather_wp`); and
calls `vg_chacha20_poly1305_seal` on them in place, by its contract
(`sealSpec_pre`, `sealSpec_post`), whose frames are in the 848 bytes below
our frame, so the return address comes back from it (`sealGather_wp`). As on
AArch64 (`Proof/ChaCha20Poly1305/AArch64/Gather/Fn.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE.SealGather VG.WriteBytes
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.Gather.PPC64LE (GatherPre gather_wp gatherRegs)

/-- The correctness of `vg_chacha20_poly1305_seal`, in its frame, by its
shared contract. -/
abbrev SealOk : Prop :=
  ∀ s, (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).pre s →
    ∃ t s', Exec isa sealCode s t s' ∧ abiPreserved s s' ∧ (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).post s s'

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, (BitVec.add_zero _).symm, by omega⟩

theorem wp_addSp {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (by simp [exec, show imm < 32768 from h]) (k _ (Upd.write _ _ _))

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 928 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 928

/-- Our frame: the stack pointer in it. -/
abbrev Pf : Addr := Bs s + BitVec.ofNat 64 848

/-- Doubleword `k` of the frame's local variable space. -/
abbrev slot (k : Nat) : Addr := Pf s + BitVec.ofNat 64 (32 + 8 * k)

/-- The frame's local variable space, which the frame makes writable, and
the whole frame. -/
abbrev FR : Region := ⟨Pf s + BitVec.ofNat 64 32, 48⟩
abbrev FA : Region := ⟨Pf s, 80⟩

/-- The memory after the entry: the back chain at `Pf`, and the slots. -/
abbrev eMem : Mem :=
  ((((((s.mem.write (Pf s) 8 s.sp).writeW (slot s 0) (s.gpr .r3)).writeW (slot s 1) (s.gpr .r4)).writeW
    (slot s 2) (s.gpr .r5)).writeW (slot s 3) (s.gpr .r6)).writeW (slot s 4) (s.gpr .r9)).writeW (slot s 5) s.lr

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_chacha20_poly1305_seal` reads and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 928
  hBn : (Bs s).toNat + 1032 ≤ 2 ^ 64
  bk : (⟨Bs s, 928⟩ : Region).Disjoint (kR s)
  bn : (⟨Bs s, 928⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 928⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 928⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 928⟩ : Region).Disjoint r
  bd : (⟨Bs s, 928⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 928⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Pf s + BitVec.ofNat 64 176, 8⟩
  w₁ : 928 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 928 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 1032 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega
  refine ⟨⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩, hB, hBn, bk, bn, ba, bds, bl, bd, bt, ?_, w₁, hgl, ods⟩
  show (⟨s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 8⟩ : Region) =
    ⟨Bs s + BitVec.ofNat 64 848 + BitVec.ofNat 64 176, 8⟩
  rw [hB, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 928) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 928⟩ :=
  Offset.sub_base _ h'

theorem slot_eq (s : State) (k : Nat) : slot s k = Bs s + BitVec.ofNat 64 (880 + 8 * k) := by
  show Bs s + BitVec.ofNat 64 848 + BitVec.ofNat 64 (32 + 8 * k) = _
  rw [Offset.add_ofNat_add_ofNat, show 848 + (32 + 8 * k) = 880 + 8 * k by omega]

/-- A slot, in the stack below the stack pointer. -/
theorem slot_sub (s : State) {k : Nat} (hk : k < 6) : (⟨slot s k, 8⟩ : Region).Sub ⟨Bs s, 928⟩ := by
  rw [slot_eq]; exact stk_sub s _ _ (by omega)

theorem slot_in (s : State) {k : Nat} (hk : k < 6) (wr : List Region) : InRegions (FR s :: wr) (slot s k) 8 :=
  ⟨_, List.mem_cons_self .., by
    show (⟨Pf s + BitVec.ofNat 64 32, 48⟩ : Region).Contains (Pf s + BitVec.ofNat 64 (32 + 8 * k)) 8
    rw [← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega) (by omega)⟩

/-- A slot, after a write to another. -/
theorem rd_sep (s : State) (m : Mem) (v : BitVec 64) {i j : Nat} (h : i ≠ j) (hi : i < 6) (hj : j < 6) :
    (m.writeW (slot s j) v).readW (slot s i) 64 = m.readW (slot s i) 64 :=
  Mem.readW_writeW_sep (Offset.sep (Pf s) (by omega) (by omega) (by omega)) (by decide)

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) := by
  have c (k : Nat) (hk : k < 6) : (FA s).Contains (slot s k) (64 / 8) :=
    Offset.contains_base _ (by omega) (by omega)
  have m := List.mem_singleton_self (FA s)
  exact ((((((Frame.refl _ _).write m _ (Region.contains_self' (by decide))).writeW m _ (c 0 (by decide))).writeW
    m _ (c 1 (by decide))).writeW m _ (c 2 (by decide))).writeW m _ (c 3 (by decide))).writeW m _ (c 4 (by decide))
    |>.writeW m _ (c 5 (by decide))

/-- The slots after the entry. -/
structure Slots (s : State) (m : Mem) : Prop where
  k : m.readW (slot s 0) 64 = s.gpr .r3
  n : m.readW (slot s 1) 64 = s.gpr .r4
  a : m.readW (slot s 2) 64 = s.gpr .r5
  al : m.readW (slot s 3) 64 = s.gpr .r6
  d : m.readW (slot s 4) 64 = s.gpr .r9
  ra : m.readW (slot s 5) 64 = s.lr

theorem slots_eMem (s : State) : Slots s (eMem s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eMem, rd_sep s _ _ (i := 0) (j := 5) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 0) (j := 4) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 0) (j := 3) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 0) (j := 2) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 0) (j := 1) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [eMem, rd_sep s _ _ (i := 1) (j := 5) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 1) (j := 4) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 1) (j := 3) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 1) (j := 2) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [eMem, rd_sep s _ _ (i := 2) (j := 5) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 2) (j := 4) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 2) (j := 3) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [eMem, rd_sep s _ _ (i := 3) (j := 5) (by decide) (by decide) (by decide),
      rd_sep s _ _ (i := 3) (j := 4) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [eMem, rd_sep s _ _ (i := 4) (j := 5) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [eMem, Mem.readW_writeW_self64]

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem pf_eq : s.sp - BitVec.ofNat 64 80 = Pf s := by
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem pf_toNat : (Pf s).toNat = (Bs s).toNat + 848 := by
  have := h.hBn
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 928⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 848 80 (by decide) x hc)

/-- `tag`, after the entry. -/
theorem eTag : (eMem s).readW (Pf s + BitVec.ofNat 64 176) 64 = Tg s := by
  rw [Frame.readW (frame_eMem s) (r := ⟨Pf s + BitVec.ofNat 64 176, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  show _ = s.mem.readW (stackArgAddr s 0) 64
  rw [show stackArgAddr s 0 = Pf s + BitVec.ofNat 64 176 from congrArg Region.base h.hargR]

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : Spec.Gcm.gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A slot, once the slices are gathered. -/
theorem gSlot {k : Nat} (hk : k < 6) : (gMem s).readW (slot s k) 64 = (eMem s).readW (slot s k) 64 :=
  Frame.readW h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.bd.sub_left (slot_sub s hk))) (by decide)

theorem slots_gMem : Slots s (gMem s) := by
  have e := slots_eMem s
  exact ⟨(h.gSlot (by decide)).trans e.k, (h.gSlot (by decide)).trans e.n, (h.gSlot (by decide)).trans e.a,
    (h.gSlot (by decide)).trans e.al, (h.gSlot (by decide)).trans e.d, (h.gSlot (by decide)).trans e.ra⟩

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  r7 : e.gpr .r7 = Src s
  r8 : e.gpr .r8 = s.gpr .r8
  r9 : e.gpr .r9 = Dst s
  r10 : e.gpr .r10 = s.gpr .r10
  r11 : e.gpr .r11 = Tg s
  r12 : e.gpr .r12 = Pf s
  pres : ∀ r ∈ preserved, e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 80 s) (Entered s) := by
  have asp : (allocated 80 s).sp = Pf s := h.pf_eq
  have awr : (allocated 80 s).wr = FR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 80 + 32, 80 - 32⟩ :: s.wr : List Region) = _
    rw [h.pf_eq]; rfl
  have amem : (allocated 80 s).mem = s.mem.write (Pf s) 8 s.sp := by
    show s.mem.write (s.sp - BitVec.ofNat 64 80) 8 s.sp = _
    rw [h.pf_eq]
  have ag (r : Reg) : (allocated 80 s).gpr r = s.gpr r := rfl
  unfold entry
  refine wp_addSp (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, asp]; exact BitVec.add_zero _
  have w₁ : u₁.wr = FR s :: s.wr := by rw [v₁.wr, awr]
  refine wp_std (a := slot s 0) (by decide) (by decide) (by rw [p₁]) (by rw [w₁]; exact slot_in s (by decide) _)
    fun u₂ v₂ => ?_
  refine wp_std (a := slot s 1) (by decide) (by decide) (by rw [v₂.gpr, p₁])
    (by rw [v₂.wr, w₁]; exact slot_in s (by decide) _) fun u₃ v₃ => ?_
  refine wp_std (a := slot s 2) (by decide) (by decide) (by rw [v₃.gpr, v₂.gpr, p₁])
    (by rw [v₃.wr, v₂.wr, w₁]; exact slot_in s (by decide) _) fun u₄ v₄ => ?_
  refine wp_std (a := slot s 3) (by decide) (by decide) (by rw [v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₄.wr, v₃.wr, v₂.wr, w₁]; exact slot_in s (by decide) _) fun u₅ v₅ => ?_
  refine wp_std (a := slot s 4) (by decide) (by decide) (by rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]; exact slot_in s (by decide) _) fun u₆ v₆ => ?_
  refine wp_mflr fun u₇ v₇ => ?_
  refine wp_std (a := slot s 5) (by decide) (by decide)
    (by rw [v₇.other _ (by decide), v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]; exact slot_in s (by decide) _) fun u₈ v₈ => ?_
  have g₆ (r : Reg) (hr : r ≠ .r12) : u₆.gpr r = s.gpr r := by
    rw [v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, v₁.other _ hr, ag]
  have g₈ (r : Reg) (h0 : r ≠ .r0) (hr : r ≠ .r12) : u₈.gpr r = s.gpr r := by
    rw [v₈.gpr, v₇.other _ h0, g₆ r hr]
  have lr₆ : u₆.lr = s.lr := by rw [v₆.lr, v₅.lr, v₄.lr, v₃.lr, v₂.lr, v₁.lr]; rfl
  have m₈ : u₈.mem = eMem s := by
    rw [v₈.mem, v₇.gpr, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, amem, lr₆, v₅.gpr, v₄.gpr,
      v₃.gpr, v₂.gpr, v₁.other .r3 (by decide), v₁.other .r4 (by decide), v₁.other .r5 (by decide),
      v₁.other .r6 (by decide), v₁.other .r9 (by decide), ag, ag, ag, ag, ag]
  have p₈ : u₈.gpr .r12 = Pf s := by rw [v₈.gpr, v₇.other _ (by decide), v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁]
  have sp₈ : u₈.sp = Pf s := by
    rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp]
  have rd₈ : u₈.rd = s.rd := by rw [v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]; rfl
  have wr₈ : u₈.wr = FR s :: s.wr := by rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]
  refine wp_ld (a := Pf s + BitVec.ofNat 64 176) (by decide) (by decide) (by rw [p₈])
    (by rw [rd₈, wr₈]; exact ⟨_, List.mem_append_left _ h.argIn, by rw [h.hargR]; exact Region.contains_self _ _⟩)
    fun u₉ v₉ => WP.block_nil ?_
  have g₉ (r : Reg) (h0 : r ≠ .r0) (h11 : r ≠ .r11) (hr : r ≠ .r12) : u₉.gpr r = s.gpr r := by
    rw [v₉.other _ h11, g₈ r h0 hr]
  have hpres : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide
  exact ⟨by rw [v₉.mem, m₈], g₉ _ (by decide) (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide),
    g₉ _ (by decide) (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide),
    by rw [v₉.gpr, m₈, h.eTag], by rw [v₉.other _ (by decide), p₈],
    fun r hr => g₉ r (hpres r hr).1 (hpres r hr).2.1 (hpres r hr).2.2, by rw [v₉.sp, sp₈], by rw [v₉.rd, rd₈],
    by rw [v₉.wr, wr₈]⟩

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bk, bn, ba, bds, bl, barg, bd, bt,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { r7 := he.r7
          r8 := by rw [he.r8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          r9 := he.r9
          hcnt := (s.gpr .r8).isLt
          dw := ods
          lt := (s.gpr .r10).isLt
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_mem fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact List.mem_append_left _ (by rw [he.rd, rd]; simp)
          lsr := fun r hr => covers_mem fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            rw [hls] at hr
            exact List.mem_append_left _ (by rw [he.rd, rd]; simp [hr])
          dw' := covers_mem fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            rw [he.wr, wr]; simp
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gMem s
  r10 : g.gpr .r10 = s.gpr .r10
  r11 : g.gpr .r11 = Tg s
  r12 : g.gpr .r12 = Pf s
  pres : ∀ r ∈ preserved, g.gpr r = s.gpr r
  sp : g.sp = Pf s
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.Gather.PPC64LE.gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  have hn : ∀ r, r ∉ gatherRegs → g.gpr r = e.gpr r := kg.gpr
  have hpres : ∀ r ∈ preserved, r ∉ gatherRegs := by decide
  exact ⟨mg, (hn _ (by decide)).trans he.r10, (hn _ (by decide)).trans he.r11, (hn _ (by decide)).trans he.r12,
    fun r hr => (hn r (hpres r hr)).trans (he.pres r hr), kg.sp.trans he.sp, kg.rd.trans he.rd,
    kg.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  r3 : c.gpr .r3 = K s
  r4 : c.gpr .r4 = Nn s
  r5 : c.gpr .r5 = Ad s
  r6 : c.gpr .r6 = s.gpr .r6
  r7 : c.gpr .r7 = Dst s
  r8 : c.gpr .r8 = s.gpr .r10
  r9 : c.gpr .r9 = Tg s
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  have sl := h.slots_gMem
  have hin {k : Nat} (hk : k < 6) (u : State) (hrd : u.rd = s.rd) (hwr : u.wr = FR s :: s.wr) :
      InRegions (u.rd ++ u.wr) (slot s k) 8 := by
    obtain ⟨r, hr, hc⟩ := slot_in s hk s.wr
    exact ⟨r, List.mem_append_right _ (by rw [hwr]; exact hr), hc⟩
  unfold callArgs
  refine wp_ld (a := slot s 0) (by decide) (by decide) (by rw [hg.r12]) (hin (by decide) _ hg.rd hg.wr)
    fun u₁ v₁ => ?_
  refine wp_ld (a := slot s 1) (by decide) (by decide) (by rw [v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₁.rd, hg.rd]) (by rw [v₁.wr, hg.wr])) fun u₂ v₂ => ?_
  refine wp_ld (a := slot s 2) (by decide) (by decide)
    (by rw [v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₂.rd, v₁.rd, hg.rd]) (by rw [v₂.wr, v₁.wr, hg.wr])) fun u₃ v₃ => ?_
  refine wp_ld (a := slot s 3) (by decide) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₃.rd, v₂.rd, v₁.rd, hg.rd]) (by rw [v₃.wr, v₂.wr, v₁.wr, hg.wr])) fun u₄ v₄ => ?_
  refine wp_ld (a := slot s 4) (by decide) (by decide)
    (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hg.rd]) (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr]))
    fun u₅ v₅ => ?_
  refine wp_mov fun u₆ v₆ => wp_mov fun u₇ v₇ => WP.block_nil ?_
  have m₄ : u₄.mem = gMem s := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem]
  have g₅ (r : Reg) (h3 : r ≠ .r3) (h4 : r ≠ .r4) (h5 : r ≠ .r5) (h6 : r ≠ .r6) (h7 : r ≠ .r7) :
      u₅.gpr r = g.gpr r := by
    rw [v₅.other _ h7, v₄.other _ h6, v₃.other _ h5, v₂.other _ h4, v₁.other _ h3]
  have g₇ (r : Reg) (h8 : r ≠ .r8) (h9 : r ≠ .r9) : u₇.gpr r = u₅.gpr r := by
    rw [v₇.other _ h9, v₆.other _ h8]
  have hpres : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 := by
    decide
  refine ⟨by rw [v₇.mem, v₆.mem, v₅.mem, m₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [g₇ _ (by decide) (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, hg.mem, sl.k]
  · rw [g₇ _ (by decide) (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.mem, hg.mem, sl.n]
  · rw [g₇ _ (by decide) (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem,
      hg.mem, sl.a]
  · rw [g₇ _ (by decide) (by decide), v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, hg.mem, sl.al]
  · rw [g₇ _ (by decide) (by decide), v₅.gpr, m₄, sl.d]
  · rw [v₇.other _ (by decide), v₆.gpr, g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.r10]
  · rw [v₇.gpr, v₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.r11]
  · obtain ⟨h3, h4, h5, h6, h7, h8, h9⟩ := hpres r hr
    rw [g₇ r h8 h9, g₅ r h3 h4 h5 h6 h7, hg.pres r hr]
  · rw [v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hg.sp]
  · rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hg.rd]
  · rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr]

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .r3 = K s ∧ c.callEntry.gpr .r4 = Nn s ∧ c.callEntry.gpr .r5 = Ad s ∧
      c.callEntry.gpr .r6 = s.gpr .r6 ∧ c.callEntry.gpr .r7 = Dst s ∧ c.callEntry.gpr .r8 = s.gpr .r10 ∧
      c.callEntry.gpr .r9 = Tg s :=
  ⟨by rw [c.callEntry_gpr (by decide), hc.r3], by rw [c.callEntry_gpr (by decide), hc.r4],
    by rw [c.callEntry_gpr (by decide), hc.r5], by rw [c.callEntry_gpr (by decide), hc.r6],
    by rw [c.callEntry_gpr (by decide), hc.r7], by rw [c.callEntry_gpr (by decide), hc.r8],
    by rw [c.callEntry_gpr (by decide), hc.r9]⟩

theorem pf_sub (s : State) : Pf s - BitVec.ofNat 64 848 = Bs s := BitVec.add_sub_cancel _ _

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9⟩ := hc.callGpr
  have hPn := h.pf_toNat
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c3, c4, c5, c6, c7, c8, c9, hc.sp, pf_sub]
    exact ⟨trivial, trivial, kd, kt, nd, nt, ad, at_, dt, h.bk.sub_left (Region.sub_prefix (by decide)),
      h.bn.sub_left (Region.sub_prefix (by decide)), h.ba.sub_left (Region.sub_prefix (by decide)),
      h.bd.sub_left (Region.sub_prefix (by decide)), h.bt.sub_left (Region.sub_prefix (by decide)),
      ok, on, oa, od, ot, by omega⟩
  · refine covers_mem fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hc.rd, hc.wr, rd, wr]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · refine covers_mem fun r hr => ?_
    rw [hc.wr, wr]
    exact List.mem_cons_of_mem _ hr

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (slot s 5) 64 = s.lr
  out : encrypt (bytesAt (gMem s) (K s) 32) (bytesAt (gMem s) (Nn s) 12) (bytesAt (gMem s) (Ad s) (AL s))
      (bytesAt (gMem s) (Dst s) (L s)) = (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem called_wp (hv : SealOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_chacha20_poly1305_seal" sealCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9⟩ := hc.callGpr
  refine WP.callAny (k := Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848) hv (sealSpec_pre hcp) hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [seal_sdepth]; decide)
  have hpost := sealSpec_post post'
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6, c7, c8, c9,
    hc.mem] at hpost
  -- The return address, from the frame, which the call kept.
  have ra : z.mem.readW (slot s 5) 64 = s.lr := by
    rw [← h.slots_gMem.ra, ← hc.mem]
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.sub_left (slot_sub s (by decide))
    · exact h.bt.sub_left (slot_sub s (by decide))
    · simp only [below, hc.sp, seal_sdepth, pf_sub, slot_eq]
      exact Offset.disjoint_base _ (by decide) (by have := h.hBn; omega)
  exact ⟨ra, hpost, fun r hr => by rw [pres' r hr, hc.pres r hr], sp'.trans hc.sp, rd'.trans hc.rd,
    wr'.trans hc.wr⟩

/-- The return address back in the link register, and the frame freed. -/
theorem ret_wp {s z : State} (h : Lay s) (hz : Called s z) :
    WP isa (.block Impl.ChaCha20Poly1305.PPC64LE.SealGather.ret) z fun y => abiPreserved s (freed 80 y) ∧ gatherPost s (freed 80 y) := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    ok, on, oa, ods, ol, od, ot, w₁, w₂, hgl, hpm⟩ := h.pre
  unfold Impl.ChaCha20Poly1305.PPC64LE.SealGather.ret
  refine wp_addSp (by decide) fun u₁ v₁ => ?_
  refine wp_ld (a := slot s 5) (by decide) (by decide) (by rw [v₁.gpr, hz.sp, BitVec.add_zero])
    (by
      obtain ⟨r, hr, hc⟩ := slot_in s (k := 5) (by decide) s.wr
      exact ⟨r, List.mem_append_right _ (by rw [v₁.wr, hz.wr]; exact hr), hc⟩) fun u₂ v₂ => ?_
  refine wp_mtlr fun u₃ v₃ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · -- The callee-saved registers.
    have hpres : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r12 := by decide
    show u₃.gpr r = s.gpr r
    rw [v₃.gpr, v₂.other _ (hpres r hr).1, v₁.other _ (hpres r hr).2, hz.pres r hr]
  · -- The stack pointer.
    show u₃.sp + BitVec.ofNat 64 80 = s.sp
    rw [v₃.sp, v₂.sp, v₁.sp, hz.sp, Offset.add_ofNat_add_ofNat, h.hB]
  · -- The link register.
    show u₃.lr = s.lr
    rw [v₃.lr, v₂.gpr, v₁.mem, hz.ra]
  · -- The ciphertext and the tag.
    show encrypt _ _ _ _ = (bytesAt u₃.mem (Dst s) (L s), bytesAt u₃.mem (Tg s) 16)
    rw [v₃.mem, v₂.mem, v₁.mem]
    have hfc : Frame [FA s, dR s] s.mem (gMem s) :=
      ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
        (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
    have apart {r : Region} (h₁ : (⟨Bs s, 928⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
        ∀ r' ∈ [FA s, dR s], r.Disjoint r' := by
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact h₁.symm.sub_right (stk_sub s 848 80 (by decide))
      · exact h₂
    have hk : bytesAt (gMem s) (K s) 32 = bytesAt s.mem (K s) 32 :=
      Proof.ChaCha20Poly1305.bytesAt_frame hfc (apart h.bk kd) (by omega)
    have hn : bytesAt (gMem s) (Nn s) 12 = bytesAt s.mem (Nn s) 12 :=
      Proof.ChaCha20Poly1305.bytesAt_frame hfc (apart h.bn nd) (by omega)
    have ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      Proof.ChaCha20Poly1305.bytesAt_frame hfc (apart h.ba ad) (by omega)
    have hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact Proof.ChaCha20Poly1305.bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (s.gpr .r10).isLt)
    have := hz.out
    rw [hk, hn, ha, hd] at this
    exact this

theorem sealGather_wp (hv : SealOk) {s : State} (hs : gatherPre s) :
    WP isa sealGather s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp hv h hc) fun z hz => ?_)
  exact ret_wp h hz

end VG.Proof.ChaCha20Poly1305.PPC64LE.Gather
