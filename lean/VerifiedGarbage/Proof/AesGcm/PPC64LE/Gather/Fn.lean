module

public import VerifiedGarbage.Proof.Gather.PPC64LE.Loop
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Callee
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: the function

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
allocates its frame of 160 bytes at `Pf = Bs + 2672`, with `Bs` the base of
the 2832 bytes of stack below the stack pointer (`sp = Bs + 2832`); keeps
`ctx`, `rounds`, `nonce`, `nonce_len`, `aad`, `aad_len` and our return
address in the seven doublewords at `Pf + 104` (`slot`), and `tag`, from
`Pf + 272`, at `Pf + 96`, the call's stack argument (`entered_wp`); gathers
the slices to `dst` (`gathered_wp`); and calls `vg_aes_gcm_seal` on them in
place, by its contract (`sealSpec_pre`, `sealSpec_post`), whose frame is in
the 2672 bytes below ours, so the return address comes back from it
(`sealGather_wp`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Fn.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)
open VG.Proof.Gather.PPC64LE (GatherPre gather_wp gatherRegs)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd LrUpd wp_std wp_ld wp_or wp_mflr wp_mtlr)

/-- The correctness of `vg_aes_gcm_seal`, in its frame, by its shared contract. -/
abbrev SealOk : Prop :=
  ∀ s, (Spec.Gcm.sealContract PPC64LE.abi 2672).pre s →
    ∃ t s', Exec isa sealCode s t s' ∧ abiPreserved s s' ∧ (Spec.Gcm.sealContract PPC64LE.abi 2672).post s s'

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, (BitVec.add_zero _).symm, by omega_arith⟩

theorem wp_addSp {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  VG.Proof.ChaCha20Poly1305.PPC64LE.WP.cons (by simp [exec, show imm < 32768 from h]) (k _ (Upd.write _ _ _))

/-- `mov d n`, an `or` of `n` with itself. -/
theorem wp_mov' {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.AesGcm.PPC64LE.mov d n :: is)) s Q :=
  wp_or fun s' u => k s' (by simpa using u)

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 2832 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 2832

/-- Our frame: the stack pointer in it. -/
abbrev Pf : Addr := Bs s + BitVec.ofNat 64 2672

/-- Doubleword `k` of what the frame keeps, and the call's stack argument. -/
abbrev slot (k : Nat) : Addr := Pf s + BitVec.ofNat 64 (104 + 8 * k)
abbrev aOut : Addr := Pf s + BitVec.ofNat 64 96

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Pf s + BitVec.ofNat 64 (256 + 8 * i)

/-- The frame past its header, which the frame makes writable, and the whole
frame. -/
abbrev FR : Region := ⟨Pf s + BitVec.ofNat 64 32, 128⟩
abbrev FA : Region := ⟨Pf s, 160⟩

/-- The memory after the entry: the back chain at `Pf`, the slots, and `tag`
for the call. -/
abbrev eMem0 : Mem :=
  (((((((s.mem.write (Pf s) 8 s.sp).writeW (slot s 0) (s.gpr .r3)).writeW (slot s 1) (s.gpr .r4)).writeW
    (slot s 2) (s.gpr .r5)).writeW (slot s 3) (s.gpr .r6)).writeW (slot s 4) (s.gpr .r7)).writeW (slot s 5)
    (s.gpr .r8)).writeW (slot s 6) s.lr

abbrev eMem : Mem := (eMem0 s).writeW (aOut s) (Tg s)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_aes_gcm_seal` reads and writes. -/
abbrev rdC : List Region := [cR s, nR s, aR s, ⟨aOut s, 8⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 2832
  hBn : (Bs s).toNat + 2952 ≤ 2 ^ 64
  bc : (⟨Bs s, 2832⟩ : Region).Disjoint (cR s)
  bn : (⟨Bs s, 2832⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 2832⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 2832⟩ : Region).Disjoint (dsR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 2832⟩ : Region).Disjoint r
  bd : (⟨Bs s, 2832⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 2832⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Pf s + BitVec.ofNat 64 256, 24⟩
  w₁ : 2832 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64
  hR : Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bc, bn, ba, bds, bl, barg, bd, bt,
    oc, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := hs
  have hB : s.sp = Bs s + BitVec.ofNat 64 2832 := (BitVec.sub_add_cancel s.sp _).symm
  have hBn : (Bs s).toNat + 2952 ≤ 2 ^ 64 := by
    have e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  refine ⟨⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bc, bn, ba, bds, bl, barg, bd, bt,
    oc, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩, hB, hBn, bc, bn, ba, bds, bl, bd, bt, ?_, w₁, hgl, ods, hR⟩
  show (⟨s.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)), 24⟩ : Region) =
    ⟨Bs s + BitVec.ofNat 64 2672 + BitVec.ofNat 64 256, 24⟩
  rw [hB, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 2832) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 2832⟩ :=
  Offset.sub_base _ h'

theorem pf_off (s : State) (a : Nat) : Pf s + BitVec.ofNat 64 a = Bs s + BitVec.ofNat 64 (2672 + a) :=
  Offset.add_ofNat_add_ofNat _ _ _

/-- A doubleword of the frame past its header, in the stack below the stack pointer. -/
theorem fr_sub (s : State) {a : Nat} (ha : a + 8 ≤ 160) :
    (⟨Pf s + BitVec.ofNat 64 a, 8⟩ : Region).Sub ⟨Bs s, 2832⟩ := by
  rw [pf_off]; exact stk_sub s _ _ (by omega_arith)

theorem fr_in (s : State) {a : Nat} (h₁ : 32 ≤ a) (h₂ : a + 8 ≤ 160) (wr : List Region) :
    InRegions (FR s :: wr) (Pf s + BitVec.ofNat 64 a) 8 :=
  ⟨_, List.mem_cons_self .., by
    show (⟨Pf s + BitVec.ofNat 64 32, 128⟩ : Region).Contains (Pf s + BitVec.ofNat 64 a) 8
    rw [show a = 32 + (a - 32) by omega_arith, ← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A doubleword of the frame, after a write to another. -/
theorem rd_sep (s : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 160)
    (hb : b + 8 ≤ 160) :
    (m.writeW (Pf s + BitVec.ofNat 64 b) v).readW (Pf s + BitVec.ofNat 64 a) 64 =
      m.readW (Pf s + BitVec.ofNat 64 a) 64 :=
  Mem.readW_writeW_sep (Offset.sep (Pf s) (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem frame_eMem0 (s : State) : Frame [FA s] s.mem (eMem0 s) := by
  have c (k : Nat) (hk : k < 7) : (FA s).Contains (slot s k) (64 / 8) :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have m := List.mem_singleton_self (FA s)
  exact (((((((Frame.refl _ _).write m _ (Region.contains_self' (by decide))).writeW m _ (c 0 (by decide))).writeW
    m _ (c 1 (by decide))).writeW m _ (c 2 (by decide))).writeW m _ (c 3 (by decide))).writeW m _ (c 4 (by decide))
    |>.writeW m _ (c 5 (by decide))).writeW m _ (c 6 (by decide))

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) :=
  (frame_eMem0 s).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

/-- The slots after the entry. -/
structure Slots (s : State) (m : Mem) : Prop where
  c : m.readW (slot s 0) 64 = s.gpr .r3
  r : m.readW (slot s 1) 64 = s.gpr .r4
  n : m.readW (slot s 2) 64 = s.gpr .r5
  nl : m.readW (slot s 3) 64 = s.gpr .r6
  a : m.readW (slot s 4) 64 = s.gpr .r7
  al : m.readW (slot s 5) 64 = s.gpr .r8
  ra : m.readW (slot s 6) 64 = s.lr
  tg : m.readW (aOut s) 64 = Tg s

theorem slots_eMem (s : State) : Slots s (eMem s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega_arith) only [eMem, eMem0, slot, aOut, rd_sep, Mem.readW_writeW_self64]

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem pf_eq : s.sp - BitVec.ofNat 64 160 = Pf s := by
  rw [h.hB, add_ofNat_sub_ofNat _ (by decide)]

theorem pf_toNat : (Pf s).toNat = (Bs s).toNat + 2672 := by
  have := h.hBn
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 = _
  show _ = s.mem.readW (Bs s + BitVec.ofNat 64 2672 + BitVec.ofNat 64 (256 + 8 * i)) 64
  rw [h.hB, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    show 2832 + (32 + 8 * (8 + i)) = 2672 + (256 + 8 * i) by omega_arith]

theorem sa_in {i : Nat} (hi : i < 3) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    show (⟨Pf s + BitVec.ofNat 64 256, 24⟩ : Region).Contains (Pf s + BitVec.ofNat 64 (256 + 8 * i)) 8
    rw [← Offset.add_ofNat_add_ofNat]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 2832⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 2672 160 (by decide) x hc)

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 3) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega_arith) (by have := h.pf_toNat; have := h.hBn; omega_arith)

/-- Our stack arguments, after the first writes of the entry and after the entry. -/
theorem e0Arg {i : Nat} (hi : i < 3) : (eMem0 s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem0 s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

theorem eArg {i : Nat} (hi : i < 3) : (eMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW (frame_eMem s) (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A doubleword of the frame, once the slices are gathered. -/
theorem gFr {a : Nat} (ha : a + 8 ≤ 160) :
    (gMem s).readW (Pf s + BitVec.ofNat 64 a) 64 = (eMem s).readW (Pf s + BitVec.ofNat 64 a) 64 :=
  Frame.readW h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.bd.sub_left (fr_sub s ha))) (by decide)

theorem slots_gMem : Slots s (gMem s) := by
  have e := slots_eMem s
  exact ⟨(h.gFr (by decide)).trans e.c, (h.gFr (by decide)).trans e.r, (h.gFr (by decide)).trans e.n,
    (h.gFr (by decide)).trans e.nl, (h.gFr (by decide)).trans e.a, (h.gFr (by decide)).trans e.al,
    (h.gFr (by decide)).trans e.ra, (h.gFr (by decide)).trans e.tg⟩

/-- Our stack arguments, once the slices are gathered. -/
theorem gArg {i : Nat} (hi : i < 3) : (gMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have darg := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [h.hargR] at darg
    refine darg.symm.sub_left ?_
    show Region.Sub ⟨Pf s + BitVec.ofNat 64 (256 + 8 * i), 8⟩ ⟨Pf s + BitVec.ofNat 64 256, 24⟩
    exact Offset.sub _ (by omega_arith) (by omega_arith)) (by decide), h.eArg hi]

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  r7 : e.gpr .r7 = Src s
  r8 : e.gpr .r8 = s.gpr .r10
  r9 : e.gpr .r9 = Dst s
  r12 : e.gpr .r12 = Pf s
  pres : ∀ r ∈ preserved, e.gpr r = s.gpr r
  sp : e.sp = Pf s
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (allocated 160 s) (Entered s) := by
  have asp : (allocated 160 s).sp = Pf s := h.pf_eq
  have awr : (allocated 160 s).wr = FR s :: s.wr := by
    show (⟨s.sp - BitVec.ofNat 64 160 + 32, 160 - 32⟩ :: s.wr : List Region) = _
    rw [h.pf_eq]; rfl
  have amem : (allocated 160 s).mem = s.mem.write (Pf s) 8 s.sp := by
    show s.mem.write (s.sp - BitVec.ofNat 64 160) 8 s.sp = _
    rw [h.pf_eq]
  have ag (r : Reg) : (allocated 160 s).gpr r = s.gpr r := rfl
  have fin : ∀ {a : Nat}, 32 ≤ a → a + 8 ≤ 160 → InRegions (FR s :: s.wr) (Pf s + BitVec.ofNat 64 a) 8 :=
    fun h₁ h₂ => fr_in s h₁ h₂ _
  unfold entry
  refine wp_addSp (by decide) fun u₁ v₁ => ?_
  have p₁ : u₁.gpr .r12 = Pf s := by rw [v₁.gpr, asp]; exact BitVec.add_zero _
  have w₁ : u₁.wr = FR s :: s.wr := by rw [v₁.wr, awr]
  refine wp_std (a := slot s 0) (by decide) (by decide) (by rw [p₁]) (by rw [w₁]; exact fin (by decide) (by decide)) fun u₂ v₂ => ?_
  refine wp_std (a := slot s 1) (by decide) (by decide) (by rw [v₂.gpr, p₁])
    (by rw [v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₃ v₃ => ?_
  refine wp_std (a := slot s 2) (by decide) (by decide) (by rw [v₃.gpr, v₂.gpr, p₁])
    (by rw [v₃.wr, v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₄ v₄ => ?_
  refine wp_std (a := slot s 3) (by decide) (by decide) (by rw [v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₄.wr, v₃.wr, v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₅ v₅ => ?_
  refine wp_std (a := slot s 4) (by decide) (by decide) (by rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₆ v₆ => ?_
  refine wp_std (a := slot s 5) (by decide) (by decide) (by rw [v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁])
    (by rw [v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]; exact fin (by decide) (by decide)) fun u₇ v₇ => ?_
  have g₇ (r : Reg) (hr : r ≠ .r12) : u₇.gpr r = s.gpr r := by
    rw [v₇.gpr, v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, v₁.other _ hr, ag]
  have p₇ : u₇.gpr .r12 = Pf s := by rw [v₇.gpr, v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, p₁]
  have w₇ : u₇.wr = FR s :: s.wr := by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, w₁]
  have rd₇ : u₇.rd = s.rd := by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd]; rfl
  have sp₇ : u₇.sp = Pf s := by rw [v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp]
  have lr₇ : u₇.lr = s.lr := by rw [v₇.lr, v₆.lr, v₅.lr, v₄.lr, v₃.lr, v₂.lr, v₁.lr]; rfl
  have m₇ : u₇.mem = ((((((s.mem.write (Pf s) 8 s.sp).writeW (slot s 0) (s.gpr .r3)).writeW (slot s 1)
      (s.gpr .r4)).writeW (slot s 2) (s.gpr .r5)).writeW (slot s 3) (s.gpr .r6)).writeW (slot s 4)
      (s.gpr .r7)).writeW (slot s 5) (s.gpr .r8) := by
    rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, amem, v₆.gpr, v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr,
      v₁.other .r3 (by decide), v₁.other .r4 (by decide), v₁.other .r5 (by decide), v₁.other .r6 (by decide),
      v₁.other .r7 (by decide), v₁.other .r8 (by decide), ag, ag, ag, ag, ag, ag]
  refine wp_mflr fun u₈ v₈ => ?_
  refine wp_std (a := slot s 6) (by decide) (by decide) (by rw [v₈.other _ (by decide), p₇])
    (by rw [v₈.wr, w₇]; exact fin (by decide) (by decide)) fun u₉ v₉ => ?_
  have m₉ : u₉.mem = eMem0 s := by rw [v₉.mem, v₈.gpr, v₈.mem, m₇, lr₇]
  refine wp_ld (a := sa s 2) (by decide) (by decide) (by rw [v₉.gpr, v₈.other _ (by decide), p₇])
    (h.sa_in (by decide) _ (by rw [v₉.rd, v₈.rd, rd₇])) fun u₁₀ v₁₀ => ?_
  refine wp_std (a := aOut s) (by decide) (by decide)
    (by rw [v₁₀.other _ (by decide), v₉.gpr, v₈.other _ (by decide), p₇])
    (by rw [v₁₀.wr, v₉.wr, v₈.wr, w₇]; exact fin (by decide) (by decide)) fun u₁₁ v₁₁ => ?_
  have m₁₁ : u₁₁.mem = eMem s := by rw [v₁₁.mem, v₁₀.gpr, v₁₀.mem, m₉, h.e0Arg (by decide)]
  refine wp_mov' fun u₁₂ v₁₂ => wp_mov' fun u₁₃ v₁₃ => ?_
  have g₁₃ (r : Reg) (h0 : r ≠ .r0) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (hr : r ≠ .r12) : u₁₃.gpr r = s.gpr r := by
    rw [v₁₃.other _ h8, v₁₂.other _ h7, v₁₁.gpr, v₁₀.other _ h0, v₉.gpr, v₈.other _ h0, g₇ r hr]
  have p₁₃ : u₁₃.gpr .r12 = Pf s := by
    rw [v₁₃.other _ (by decide), v₁₂.other _ (by decide), v₁₁.gpr, v₁₀.other _ (by decide), v₉.gpr,
      v₈.other _ (by decide), p₇]
  have rd₁₃ : u₁₃.rd = s.rd := by rw [v₁₃.rd, v₁₂.rd, v₁₁.rd, v₁₀.rd, v₉.rd, v₈.rd, rd₇]
  have wr₁₃ : u₁₃.wr = FR s :: s.wr := by rw [v₁₃.wr, v₁₂.wr, v₁₁.wr, v₁₀.wr, v₉.wr, v₈.wr, w₇]
  have sp₁₃ : u₁₃.sp = Pf s := by rw [v₁₃.sp, v₁₂.sp, v₁₁.sp, v₁₀.sp, v₉.sp, v₈.sp, sp₇]
  have m₁₃ : u₁₃.mem = eMem s := by rw [v₁₃.mem, v₁₂.mem, m₁₁]
  refine wp_ld (a := sa s 0) (by decide) (by decide) (by rw [p₁₃]) (h.sa_in (by decide) _ rd₁₃)
    fun u₁₄ v₁₄ => WP.block_nil ?_
  have hpres : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r12 := by decide
  refine ⟨by rw [v₁₄.mem, m₁₃], ?_, ?_, by rw [v₁₄.gpr, m₁₃, h.eArg (by decide)], by
    rw [v₁₄.other _ (by decide), p₁₃], fun r hr => ?_, by rw [v₁₄.sp, sp₁₃], by rw [v₁₄.rd, rd₁₃],
    by rw [v₁₄.wr, wr₁₃]⟩
  · rw [v₁₄.other _ (by decide), v₁₃.other _ (by decide), v₁₂.gpr, v₁₁.gpr, v₁₀.other _ (by decide), v₉.gpr,
      v₈.other _ (by decide), g₇ _ (by decide)]
  · rw [v₁₄.other _ (by decide), v₁₃.gpr, v₁₂.other _ (by decide), v₁₁.gpr, v₁₀.other _ (by decide), v₉.gpr,
      v₈.other _ (by decide), g₇ _ (by decide)]
  · obtain ⟨h0, h7, h8, h9, h12⟩ := hpres r hr
    rw [v₁₄.other _ h9, g₁₃ r h0 h7 h8 h12]

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, bc, bn, ba, bds, bl, barg, bd, bt,
    oc, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { r7 := he.r7
          r8 := by rw [he.r8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          r9 := he.r9
          hcnt := (s.gpr .r10).isLt
          dw := ods
          lt := (stackArg s 1).isLt
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
  exact ⟨mg, (hn _ (by decide)).trans he.r12, fun r hr => (hn r (hpres r hr)).trans (he.pres r hr),
    kg.sp.trans he.sp, kg.rd.trans he.rd, kg.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  r3 : c.gpr .r3 = C s
  r4 : c.gpr .r4 = s.gpr .r4
  r5 : c.gpr .r5 = Nn s
  r6 : c.gpr .r6 = s.gpr .r6
  r7 : c.gpr .r7 = Ad s
  r8 : c.gpr .r8 = s.gpr .r8
  r9 : c.gpr .r9 = Dst s
  r10 : c.gpr .r10 = stackArg s 1
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  sp : c.sp = Pf s
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  have sl := h.slots_gMem
  have hin {k : Nat} (hk : k < 7) (u : State) (hwr : u.wr = FR s :: s.wr) : InRegions (u.rd ++ u.wr) (slot s k) 8 := by
    obtain ⟨r, hr, hc⟩ := fr_in s (a := 104 + 8 * k) (by omega_arith) (by omega_arith) s.wr
    exact ⟨r, List.mem_append_right _ (by rw [hwr]; exact hr), hc⟩
  unfold callArgs
  refine wp_ld (a := slot s 0) (by decide) (by decide) (by rw [hg.r12]) (hin (by decide) _ hg.wr) fun u₁ v₁ => ?_
  refine wp_ld (a := slot s 1) (by decide) (by decide) (by rw [v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₁.wr, hg.wr])) fun u₂ v₂ => ?_
  refine wp_ld (a := slot s 2) (by decide) (by decide)
    (by rw [v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₂.wr, v₁.wr, hg.wr])) fun u₃ v₃ => ?_
  refine wp_ld (a := slot s 3) (by decide) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₃.wr, v₂.wr, v₁.wr, hg.wr])) fun u₄ v₄ => ?_
  refine wp_ld (a := slot s 4) (by decide) (by decide)
    (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), hg.r12])
    (hin (by decide) _ (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr])) fun u₅ v₅ => ?_
  have g₅ (r : Reg) (h3 : r ≠ .r3) (h4 : r ≠ .r4) (h5 : r ≠ .r5) (h6 : r ≠ .r6) (h7 : r ≠ .r7) :
      u₅.gpr r = g.gpr r := by
    rw [v₅.other _ h7, v₄.other _ h6, v₃.other _ h5, v₂.other _ h4, v₁.other _ h3]
  have m₅ : u₅.mem = gMem s := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem]
  have rd₅ : u₅.rd = s.rd := by rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hg.rd]
  have wr₅ : u₅.wr = FR s :: s.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr]
  have p₅ : u₅.gpr .r12 = Pf s := by
    rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.r12]
  refine wp_ld (a := slot s 5) (by decide) (by decide) (by rw [p₅]) (hin (by decide) _ wr₅) fun u₆ v₆ => ?_
  refine wp_ld (a := sa s 0) (by decide) (by decide) (by rw [v₆.other _ (by decide), p₅])
    (h.sa_in (by decide) _ (by rw [v₆.rd, rd₅])) fun u₇ v₇ => ?_
  refine wp_ld (a := sa s 1) (by decide) (by decide) (by rw [v₇.other _ (by decide), v₆.other _ (by decide), p₅])
    (h.sa_in (by decide) _ (by rw [v₇.rd, v₆.rd, rd₅])) fun u₈ v₈ => WP.block_nil ?_
  have g₈ (r : Reg) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h10 : r ≠ .r10) : u₈.gpr r = u₅.gpr r := by
    rw [v₈.other _ h10, v₇.other _ h9, v₆.other _ h8]
  have m₈ : u₈.mem = gMem s := by rw [v₈.mem, v₇.mem, v₆.mem, m₅]
  have hpres : ∀ r ∈ preserved,
      r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 := by decide
  refine ⟨m₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [g₈ _ (by decide) (by decide) (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hg.mem, sl.c]
  · rw [g₈ _ (by decide) (by decide) (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.mem, hg.mem, sl.r]
  · rw [g₈ _ (by decide) (by decide) (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem,
      v₁.mem, hg.mem, sl.n]
  · rw [g₈ _ (by decide) (by decide) (by decide), v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, hg.mem,
      sl.nl]
  · rw [g₈ _ (by decide) (by decide) (by decide), v₅.gpr, v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem, sl.a]
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr, m₅, sl.al]
  · rw [v₈.other _ (by decide), v₇.gpr, v₆.mem, m₅, h.gArg (by decide)]
  · rw [v₈.gpr, v₇.mem, v₆.mem, m₅, h.gArg (by decide)]
  · obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpres r hr
    rw [g₈ r h8 h9 h10, g₅ r h3 h4 h5 h6 h7, hg.pres r hr]
  · rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hg.sp]
  · rw [v₈.rd, v₇.rd, v₆.rd, rd₅]
  · rw [v₈.wr, v₇.wr, v₆.wr, wr₅]

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .r3 = C s ∧ c.callEntry.gpr .r4 = s.gpr .r4 ∧ c.callEntry.gpr .r5 = Nn s ∧
      c.callEntry.gpr .r6 = s.gpr .r6 ∧ c.callEntry.gpr .r7 = Ad s ∧ c.callEntry.gpr .r8 = s.gpr .r8 ∧
      c.callEntry.gpr .r9 = Dst s ∧ c.callEntry.gpr .r10 = stackArg s 1 :=
  ⟨by rw [c.callEntry_gpr (by decide), hc.r3], by rw [c.callEntry_gpr (by decide), hc.r4],
    by rw [c.callEntry_gpr (by decide), hc.r5], by rw [c.callEntry_gpr (by decide), hc.r6],
    by rw [c.callEntry_gpr (by decide), hc.r7], by rw [c.callEntry_gpr (by decide), hc.r8],
    by rw [c.callEntry_gpr (by decide), hc.r9], by rw [c.callEntry_gpr (by decide), hc.r10]⟩

theorem pf_sub (s : State) : Pf s - BitVec.ofNat 64 2672 = Bs s := BitVec.add_sub_cancel _ _

/-- The call's stack argument, in its own terms. -/
theorem Ready.argAddr {s c : State} (hc : Ready s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = aOut s := by
  show c.sp + BitVec.ofNat 64 (32 + 8 * (8 + 0)) = Pf s + BitVec.ofNat 64 96
  rw [hc.sp]

theorem Ready.arg {s c : State} (h : Lay s) (hc : Ready s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s := by
  show c.mem.readW (stackArgAddr ((c.callEntry).withRegions rd wr) 0) 64 = _
  rw [hc.argAddr, hc.mem, h.slots_gMem.tg]

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    oc, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr
  have hPn := h.pf_toNat
  have hBn := h.hBn
  have aS : (⟨aOut s, 8⟩ : Region).Sub ⟨Bs s, 2832⟩ := fr_sub s (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, c3, c4, c5, c6, c7, c8, c9, c10, hc.sp, pf_sub, hc.argAddr, hc.arg h]
    refine ⟨trivial, trivial, cd, ct, nd, nt, ad, at_, dt, h.bd.symm.sub_right aS, h.bt.symm.sub_right aS,
      h.bc.sub_left (Region.sub_prefix (by decide)), h.bn.sub_left (Region.sub_prefix (by decide)),
      h.ba.sub_left (Region.sub_prefix (by decide)), h.bd.sub_left (Region.sub_prefix (by decide)),
      h.bt.sub_left (Region.sub_prefix (by decide)), ?_, oc, on, oa, od, ot, by omega_arith, by omega_arith, hR⟩
    show (⟨Bs s, 2672⟩ : Region).Disjoint ⟨Bs s + BitVec.ofNat 64 2672 + BitVec.ofNat 64 96, 8⟩
    rw [Offset.add_ofNat_add_ofNat]
    exact (Offset.disjoint_base _ (by decide) (by omega_arith)).symm
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · refine ⟨FR s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 64, ?_, by show 64 + 8 ≤ 128; omega_arith⟩
      exact (Offset.add_ofNat_add_ofNat (Pf s) 32 64).symm
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
  · refine covers_mem fun r hr => ?_
    rw [hc.wr, wr]
    exact List.mem_cons_of_mem _ hr

/-- Changes confined to the caller frame and destination keep the encryption inputs. -/
theorem Lay.encrypt_frame {s : State} (h : Lay s) {m : Mem} (hf : Frame [FA s,dR s] s.mem m)
    (plaintext : List Byte) :
    encryptWith (ctxCiph m (C s) (Rn s)) (ctxH m (C s)) 16 (bytesAt m (Nn s) (NL s)) plaintext
        (bytesAt m (Ad s) (AL s)) =
      encryptWith (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) 16 (bytesAt s.mem (Nn s) (NL s)) plaintext
        (bytesAt s.mem (Ad s) (AL s)) := by
  obtain ⟨-, -, cd, -, nd, -, ad, -⟩ := h.pre
  have apart {r : Region} (h₁ : (⟨Bs s,2832⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r'∈[FA s,dR s],r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
    rcases hr' with rfl|rfl
    · exact h₁.symm.sub_right (stk_sub s 2672 160 (by decide))
    · exact h₂
  obtain ⟨hctx,hhash⟩ := Proof.AesGcm.ctx_frame hf (apart h.bc cd) h.hR
  have hn : bytesAt m (Nn s) (NL s)=bytesAt s.mem (Nn s) (NL s) :=
    Proof.Cmac.bytesAt_frame hf (apart h.bn nd) (Nat.le_of_lt (s.gpr .r6).isLt)
  have ha : bytesAt m (Ad s) (AL s)=bytesAt s.mem (Ad s) (AL s) :=
    Proof.Cmac.bytesAt_frame hf (apart h.ba ad) (Nat.le_of_lt (s.gpr .r8).isLt)
  rw [hctx,hhash,hn,ha]

/-- The original full-gather view encrypts the same plaintext as the caller. -/
theorem Lay.gMem_encrypt {s : State} (h : Lay s) :
    encryptWith (ctxCiph (gMem s) (C s) (Rn s)) (ctxH (gMem s) (C s)) 16
        (bytesAt (gMem s) (Nn s) (NL s)) (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
      encryptWith (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) 16
        (bytesAt s.mem (Nn s) (NL s)) (pt s (Cnt s)) (bytesAt s.mem (Ad s) (AL s)) := by
  have hf : Frame [FA s,dR s] s.mem (gMem s) :=
    ((frame_eMem s).mono (fun r hr => by rw [List.mem_singleton] at hr; subst r; simp)).trans
      (h.frame_gMem.mono (fun r hr => by rw [List.mem_singleton] at hr; subst r; simp))
  have hd : bytesAt (gMem s) (Dst s) (L s)=pt s (Cnt s) := by
    rw [← h.hlen]
    exact Proof.AesGcm.bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (stackArg s 1).isLt)
  rw [hd]
  exact h.encrypt_frame hf _

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (slot s 6) 64 = s.lr
  out : encryptWith (ctxCiph (gMem s) (C s) (Rn s)) (ctxH (gMem s) (C s)) 16 (bytesAt (gMem s) (Nn s) (NL s))
      (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
    (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Pf s
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr

theorem called_wp (hv : SealOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_aes_gcm_seal" sealCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr
  refine WP.callAny (k := Spec.Gcm.sealContract PPC64LE.abi 2672) hv (sealSpec_pre hcp) hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [seal_sdepth]; decide)
  have hpost := sealSpec_post post' (by simp only [State.withRegions_gpr, c4]; exact h.hR)
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6, c7, c8, c9, c10,
    hc.mem, hc.arg h] at hpost
  -- The return address, from the frame, which the call kept.
  have ra : z.mem.readW (slot s 6) 64 = s.lr := by
    rw [← h.slots_gMem.ra, ← hc.mem]
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.sub_left (fr_sub s (by decide))
    · exact h.bt.sub_left (fr_sub s (by decide))
    · simp only [below, hc.sp, seal_sdepth, pf_sub, slot, pf_off]
      exact Offset.disjoint_base _ (by decide) (by have := h.hBn; omega_arith)
  exact ⟨ra, hpost, fun r hr => by rw [pres' r hr, hc.pres r hr], sp'.trans hc.sp, rd'.trans hc.rd,
    wr'.trans hc.wr⟩

/-- The return address back in the link register, and the frame freed. -/
theorem ret_wp {s z : State} (h : Lay s) (hz : Called s z) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealGather.ret) z fun y => abiPreserved s (freed 160 y) ∧ gatherPost s (freed 160 y) := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, lsdt, dt, darg, targ, -, -, -, -, -, -, -, -,
    oc, on, oa, ods, ol, od, ot, w₁, w₂, hR, hgl⟩ := h.pre
  unfold Impl.AesGcm.PPC64LE.SealGather.ret
  refine wp_addSp (by decide) fun u₁ v₁ => ?_
  refine wp_ld (a := slot s 6) (by decide) (by decide) (by rw [v₁.gpr, hz.sp, BitVec.add_zero])
    (by
      obtain ⟨r, hr, hc⟩ := fr_in s (a := 104 + 8 * 6) (by decide) (by decide) s.wr
      exact ⟨r, List.mem_append_right _ (by rw [v₁.wr, hz.wr]; exact hr), hc⟩) fun u₂ v₂ => ?_
  refine wp_mtlr fun u₃ v₃ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · -- The callee-saved registers.
    have hpres : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r12 := by decide
    show u₃.gpr r = s.gpr r
    rw [v₃.gpr, v₂.other _ (hpres r hr).1, v₁.other _ (hpres r hr).2, hz.pres r hr]
  · -- The stack pointer.
    show u₃.sp + BitVec.ofNat 64 160 = s.sp
    rw [v₃.sp, v₂.sp, v₁.sp, hz.sp, Offset.add_ofNat_add_ofNat, h.hB]
  · -- The link register.
    show u₃.lr = s.lr
    rw [v₃.lr, v₂.gpr, v₁.mem, hz.ra]
  · -- The ciphertext and the tag.
    show encryptWith _ _ _ _ _ _ = (bytesAt u₃.mem (Dst s) (L s), bytesAt u₃.mem (Tg s) 16)
    rw [v₃.mem, v₂.mem, v₁.mem]
    have out := hz.out
    rw [h.gMem_encrypt] at out
    exact out

theorem sealGather_wp (hv : SealOk) {s : State} (hs : gatherPre s) :
    WP isa sealGather s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := h.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp hv h hc) fun z hz => ?_)
  exact ret_wp h hz

end VG.Proof.AesGcm.PPC64LE.Gather
