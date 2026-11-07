module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneShot
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Open.lean`): `open` checks the tag length; if it is
allowed, it computes the tag of the ciphertext into `W + 112` (`oneAad`,
`oneTag 112`), copies the received tag to `W + 256` and compares the first
`tag_len` bytes of each (`recv`, `cmp 112`), and decrypts the data in place
only if they are equal; `a0` is the result (`open_wp`). Until the data is
decrypted, everything `open` writes is in the working space `W` or the stack
below `sp` (`Frame (wF W sp)`), which every buffer is apart from.

The same proof is `vg_aes_gcm_open_to`'s body (`openWith true`), which reads
the ciphertext at `a6` and writes the plaintext to a destination `Dst`
apart from it: `open_head` and `open_tail` take what the body needs of its
arguments (`OPre o`), wherever the entry found them, and the state after the
entry (`SO2`); in place, `Dst` is the data itself (`openPre.opre`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph fullTag zeros padLen j0 inc32 gctr decryptWith openResult)

/-- What `open` promises, given the result `a0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .a0 = 1 ∧ bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = pt
  | none => s.gpr .a0 = 0 ∧ bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .a0 = 0)
    (hd : bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .a0 = 1)
    (hd : bytesAt s.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- What the end of `open` leaves for `restore`. -/
structure OpenOut (s₀ s : State) : Prop where
  s0 : s.gpr .s0 = stackArg s₀ 2
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem (stackArg s₀ 2) s₀
  post : OpenPost s₀ s

/-- An environment for a state's own registers, after a step that changes
only registers the pieces do not need pinned: `s0`–`s2` and the regions are
kept. -/
theorem Env.self' {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (h0 : s'.gpr .s0 = s.gpr .s0) (h1 : s'.gpr .s1 = s.gpr .s1) (h2 : s'.gpr .s2 = s.gpr .s2) (hk : Keeps s s') :
    Env s'.gpr sp s' :=
  ⟨fun _ _ => rfl, hk.sp.trans he.sp, by
    rw [h2, h1, h0, he.fr _ (by decide), he.fr _ (by decide), he.fr _ (by decide)]
    exact he.perm.of_eq hk.rd hk.wr, by
    rw [h2, h1, h0, he.fr _ (by decide), he.fr _ (by decide), he.fr _ (by decide), hk.sp]
    exact he.stk⟩

/-- An environment for a state's own registers, after a step that changes
only `s8` among those the environment pins. -/
theorem Env.self {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (he : Env V sp s)
    (hg : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r) (hk : Keeps s s') : Env s'.gpr sp s' :=
  he.self' (hg _ (by decide)) (hg _ (by decide)) (hg _ (by decide)) hk

/-- `W` and the stack below `sp`. -/
abbrev wF (W sp : Addr) : List Region := [⟨W, 2560⟩, below sp 2048]

section
variable {W sp : Addr}

/-- What `oneAad`, `oneTag 112`, `recv` and `cmp 112` write is in `W` or below `sp`. -/
theorem inW_j0 : ∀ r ∈ j0Frame (W + BitVec.ofNat 64 16) W sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem inW_ot : ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem inW_at {d : Nat} (hd : d + 16 ≤ 2560) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub hd⟩

theorem inW_one : ∀ r ∈ [oneR W], ∃ r' ∈ wF W sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩

/-- The first counter block is apart from what `oneTag 112`, `recv` and `cmp 112` write. -/
theorem cb_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := W + BitVec.ofNat 64 16) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide))
      (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hk.st.sub_left (Lay.stSub (by decide))
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)

/-- A slot of the addresses (`W + d`, `232 ≤ d < 256`) is apart from what
`oneTag 112`, `recv` and `cmp 112` write. -/
theorem slot_ot {c : Addr} (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp)
    {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩],
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega, by omega⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega))
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)

end

/-- A buffer apart from `W` and the stack below `sp` is as it was. -/
theorem bytes_W {m m' : Mem} {W sp p : Addr} {n : Nat} (hf : Frame (wF W sp) m m')
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hs : (⟨p, n⟩ : Region).Disjoint (below sp 2048)) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd
    · exact hs) hn

/-- Whether the computed tag, cut to the tag length `TL`, is the received
one at `T`. -/
abbrev OpenTagOk (s₀ : State) (T : Addr) (TL : Nat) : Prop :=
  (fullTag (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat) (ctxH s₀.mem (s₀.gpr .a0))
      (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat) (bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat)
      (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)).take TL = bytesAt s₀.mem T TL

/-- `OpenTagOk` for `vg_aes_gcm_open`'s tag, its first two stack arguments. -/
abbrev openTagOk (s₀ : State) : Prop := OpenTagOk s₀ (stackArg s₀ 0) (stackArg s₀ 1).toNat

/-- What `open`'s body needs of its arguments: the context, nonce, additional
data and data in `a0`–`a7`, the working space `W` and the tag `T` of `TL`
bytes, wherever the entry found them, and where the plaintext goes, `Dst`:
the data itself in place (`o` false), or a buffer apart from it. -/
structure OPre (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) : Prop where
  ctx : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)
  nonce : Covers [⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩] (s₀.rd ++ s₀.wr)
  aad : Covers [⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩] (s₀.rd ++ s₀.wr)
  src : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] (s₀.rd ++ s₀.wr)
  tag : Covers [⟨T, TL⟩] (s₀.rd ++ s₀.wr)
  w : Covers [⟨W, 2560⟩] s₀.wr
  dst : Covers [⟨Dst, (s₀.gpr .a7).toNat⟩] s₀.wr
  dcW : (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint ⟨W, 2560⟩
  dnW : (⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  daW : (⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  dsW : (⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  dtW : (⟨T, TL⟩ : Region).Disjoint ⟨W, 2560⟩
  dDW : (⟨Dst, (s₀.gpr .a7).toNat⟩ : Region).Disjoint ⟨W, 2560⟩
  dcD : (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint ⟨Dst, (s₀.gpr .a7).toNat⟩
  fc : (s₀.gpr .a0).toNat + 256 ≤ 2 ^ 64
  fn : (s₀.gpr .a2).toNat + (s₀.gpr .a3).toNat ≤ 2 ^ 64
  fa : (s₀.gpr .a4).toNat + (s₀.gpr .a5).toNat ≤ 2 ^ 64
  fs : (s₀.gpr .a6).toNat + (s₀.gpr .a7).toNat ≤ 2 ^ 64
  fD : Dst.toNat + (s₀.gpr .a7).toNat ≤ 2 ^ 64
  fW : W.toNat + 2560 ≤ 2 ^ 64
  tl : TL < 2 ^ 64
  bufs : ∀ r ∈ [(⟨s₀.gpr .a0, 256⟩ : Region), ⟨s₀.gpr .a2, (s₀.gpr .a3).toNat⟩,
    ⟨s₀.gpr .a4, (s₀.gpr .a5).toNat⟩, ⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩, ⟨Dst, (s₀.gpr .a7).toNat⟩, ⟨T, TL⟩,
    ⟨W, 2560⟩], r.Disjoint (below s₀.sp 2048)
  al : s₀.sp.toNat % 16 = 0
  ge : 2048 ≤ s₀.sp.toNat
  rounds : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14
  ca : (s₀.gpr .a0).toNat % 8 = 0
  wa : W.toNat % 8 = 0
  alias : Alias o (s₀.gpr .a6) Dst (s₀.gpr .a7).toNat

section
variable {o : Bool} {s₀ : State} {W T Dst : Addr} {TL : Nat} (h : OPre o s₀ W T Dst TL)
include h

theorem OPre.lay : Lay (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W := oneLay h.fc h.fW h.dcW h.ca h.wa

theorem OPre.stk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp :=
  ⟨h.bufs _ (by simp), (h.bufs _ (by simp)).sub_left (Lay.wSub (by decide)), h.bufs _ (by simp), h.al, h.ge⟩

theorem OPre.dsrc : DataOk (W + BitVec.ofNat 64 16) W s₀ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
  ⟨h.src, (s₀.gpr .a7).isLt, h.fs, h.dsW.sub_right (Lay.wSub (by decide)), h.dsW, h.bufs _ (by simp)⟩

theorem OPre.ddst : DataW (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀ Dst (s₀.gpr .a7).toNat :=
  ⟨⟨covers_left h.dst, (s₀.gpr .a7).isLt, h.fD, h.dDW.sub_right (Lay.wSub (by decide)), h.dDW,
    h.bufs _ (by simp)⟩, h.dst, h.dcD⟩

end

/-- In place: `vg_aes_gcm_open`'s precondition. -/
theorem openPre.opre {s₀ : State} (h : openPre s₀) :
    OPre false s₀ (stackArg s₀ 2) (stackArg s₀ 0) (s₀.gpr .a6) (stackArg s₀ 1).toNat := by
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hR, hstk,
    ca, wa⟩ := h
  have mr : ∀ {r : Region}, r ∈ s₀.rd → Covers [r] (s₀.rd ++ s₀.wr) := fun h =>
    covers_mem (List.mem_append_left _ h)
  have hD : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  exact ⟨mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), mr (by rw [hrd]; simp), covers_left hD,
    mr (by rw [hrd]; simp), by rw [hwr]; exact covers_mem (by simp), hD, dcW, dnW, daW, ddW, dtW, ddW, dcd, fc,
    fn, fa, fd, fd, fW, (stackArg s₀ 1).isLt, fun r hr => hstk.buf (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h <;> subst h <;> simp), hstk.1, hstk.2.1,
    hR, ca, wa, rfl⟩

/-- After the entry of `open`'s body, from `s₀`, with the working space `W`
and the tag's address `T`: `SO1`, but for the slots the entry writes, and,
out of place, the distance to the destination at `W + dstO`. -/
structure SO2 (o : Bool) (W T Dst : Addr) (s₀ s₁ : State) : Prop where
  keeps : Keeps' s₀ s₁
  saved : SavedAt s₁.mem W s₀
  frame : Frame (wF W s₀.sp) s₀.mem s₁.mem
  aad : s₁.mem.readW (W + BitVec.ofNat 64 aadO) 64 = s₀.gpr .a4
  dat : s₁.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s₁.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  s0 : s₁.gpr .s0 = W
  s1 : s₁.gpr .s1 = W + BitVec.ofNat 64 16
  s2 : s₁.gpr .s2 = s₀.gpr .a0
  s3 : s₁.gpr .s3 = s₀.gpr .a1
  s4 : s₁.gpr .s4 = s₀.gpr .a2
  s5 : s₁.gpr .s5 = s₀.gpr .a3
  s7 : s₁.gpr .s7 = s₀.gpr .a3
  s10 : s₁.gpr .s10 = s₀.gpr .a5
  s11 : s₁.gpr .s11 = s₀.gpr .a7
  s9 : s₁.gpr .s9 = T

/-- In place, `SO1`. -/
theorem SO1.so2 {W T Dst : Addr} {s₀ s₁ : State} (h : SO1 W T s₀ s₁) : SO2 false W T Dst s₀ s₁ :=
  ⟨h.keeps, h.saved, h.frame.sub inW_one, h.aad, h.dat, nofun, h.s0, h.s1, h.s2, h.s3, h.s4, h.s5, h.s7,
    h.s10, h.s11, h.s9⟩

/-- After a step that changes no register the entry set but `t0` and `s8`. -/
theorem SO2.keep {o : Bool} {W T Dst : Addr} {s₀ s₁ s₂ : State} (h1 : SO2 o W T Dst s₀ s₁)
    (hg : ∀ r, r ≠ .t0 → r ≠ .s8 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO2 o W T Dst s₀ s₂ :=
  ⟨⟨hk.rd.trans h1.keeps.rd, hk.wr.trans h1.keeps.wr, hk.sp.trans h1.keeps.sp⟩, hk.mem ▸ h1.saved,
    hk.mem ▸ h1.frame, hk.mem ▸ h1.aad, hk.mem ▸ h1.dat, fun ho => hk.mem ▸ h1.dst ho,
    by rw [hg _ (by decide) (by decide)]; exact h1.s0, by rw [hg _ (by decide) (by decide)]; exact h1.s1,
    by rw [hg _ (by decide) (by decide)]; exact h1.s2, by rw [hg _ (by decide) (by decide)]; exact h1.s3,
    by rw [hg _ (by decide) (by decide)]; exact h1.s4, by rw [hg _ (by decide) (by decide)]; exact h1.s5,
    by rw [hg _ (by decide) (by decide)]; exact h1.s7, by rw [hg _ (by decide) (by decide)]; exact h1.s10,
    by rw [hg _ (by decide) (by decide)]; exact h1.s11, by rw [hg _ (by decide) (by decide)]; exact h1.s9⟩

/-- After the entry, the environment. -/
theorem SO2.env {o : Bool} {W T Dst : Addr} {s₀ s₁ : State} (h1 : SO2 o W T Dst s₀ s₁)
    (hC : Covers [⟨s₀.gpr .a0, 256⟩] (s₀.rd ++ s₀.wr)) (hW : Covers [⟨W, 2560⟩] s₀.wr)
    (hk : StkOk (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀.sp) :
    Env s₁.gpr s₀.sp s₁ := by
  have perm : Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₁ :=
    (⟨hC, covers_off hW (show 16 + 80 ≤ 2560 by decide) (by decide), hW⟩ :
      Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₀).of_eq h1.keeps.rd h1.keeps.wr
  exact ⟨fun _ _ => rfl, h1.keeps.sp, by rw [h1.s2, h1.s1, h1.s0]; exact perm,
    by rw [h1.s2, h1.s1, h1.s0, h1.keeps.sp]; exact hk⟩

/-- After the tags are compared, with the result in `s8` and, out of place,
the distance to the destination in `s9`, from `s₄` (after the entry). -/
structure OpenMid (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) (s₄ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  regs : ∀ r ∈ frozen, r ≠ .s8 → r ≠ .s9 → s.gpr r = s₄.gpr r
  rd : s.rd = s₄.rd
  wr : s.wr = s₄.wr
  saved : SavedAt s.mem W s₀
  frame : Frame (wF W s₀.sp) s₀.mem s.mem
  cb : blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat))
  dat : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  s8 : s.gpr .s8 = BitVec.ofNat 64 (if OpenTagOk s₀ T TL then 1 else 0)
  s9 : o = true → s.gpr .s9 = Dst - s₀.gpr .a6

/-- Out of place, the distance into `s9`; in place, nothing. -/
theorem deltaArg_ok {o : Bool} {s : State} {W δ : Addr} (h31 : s.gpr .s0 = W) (wa : W.toNat % 8 = 0)
    (hW : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 dstO) 8)
    (hδ : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = δ) :
    WP isa (.block (deltaArg o)) s fun s' => (o = true → s'.gpr .s9 = δ) ∧
      (∀ r, r ≠ .s9 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  cases o
  · simp only [deltaArg, Bool.false_eq_true, ↓reduceIte]
    exact WP.block_nil ⟨nofun, fun _ _ => rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  · simp only [deltaArg, ↓reduceIte]
    exact Steps.wp_ld (off := dstO) (a := W + BitVec.ofNat 64 dstO) (by decide) (by rw [h31])
      (Spill.al8 wa (by decide)) hW fun s₁ u₁ => WP.block_nil ⟨fun _ => by rw [u₁.gpr, hδ rfl],
        fun r hr => u₁.other r hr, ⟨u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩⟩

/-- `open`'s body, once the tag length is allowed, up to the comparison of
the tags (and, out of place, the distance loaded into `s9`), followed by any
`T'`. -/
theorem open_head [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Bool} {s₀ s₄ : State} {W T Dst : Addr} {TL : Nat}
    (h : OPre o s₀ W T Dst TL) (h4 : SO2 o W T Dst s₀ s₄)
    (h19 : s₄.gpr .s8 = BitVec.ofNat 64 TL) (hok : Spec.Gcm.tagLenOk TL = true) {T' : Prog isa}
    {Q : State → Prop} (k : ∀ s₉, OpenMid o s₀ W T Dst TL s₄ s₉ → WP isa T' s₉ Q) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112)
      (.seq (.block ([mov .s8 .a0] ++ deltaArg o)) T'))))) s₄ Q := by
  have L₀ := h.lay
  have hk₀ := h.stk
  have hR := h.rounds
  have wa := h.wa
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  have he₄ := h4.env h.ctx h.w hk₀
  have L := L₀.v h4.s2 h4.s1 h4.s0
  have hk₄ := h4.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ wF W s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dcW
    · exact hk₀.c
  have F₄ : Frame (wF W s₀.sp) s₀.mem s₄.mem := h4.frame
  -- `oneAad`
  have hN : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a2) (s₀.gpr .a3).toNat := by
    rw [h4.s1, h4.s0]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.nonce, (s₀.gpr .a3).isLt, h.fn, h.dnW.sub_right (Lay.wSub (by decide)),
      h.dnW, by rw [hk₄.sp]; exact h.bufs _ (by simp)⟩
  have hAd : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a4) (s₄.gpr .s10).toNat := by
    rw [h4.s1, h4.s0, h4.s10]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.aad, (s₀.gpr .a5).isLt, h.fa, h.daW.sub_right (Lay.wSub (by decide)),
      h.daW, by rw [hk₄.sp]; exact h.bufs _ (by simp)⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.s4 (by rw [h4.s5]; exact toN)
    (by rw [h4.s7]; exact toN) hN hAd (by rw [h4.s0]; exact h4.aad))) fun s₅ ⟨oa, rd₅, wr₅, sp₅⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.s1, h4.s0] at f₅
  have F₅ : Frame (wF W s₀.sp) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  have hs₄ : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a6) (s₄.gpr .s11).toNat := by
    rw [h4.s1, h4.s0, h4.s11]; exact h.dsrc.of_eq hk₄.rd hk₄.wr hk₄.sp
  have h28 : s₄.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h4.s3]; exact toN
  have dat₅ : s₅.mem.readW (s₄.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oa.frame (slot_j0 L he₄.stk' (by decide)), h4.s0]; exact h4.dat
  have dst₅ : o = true → s₅.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6 := fun ho => by
    rw [← h4.s0, slot_keep oa.frame (slot_j0' L he₄.stk' (d := dstO) (by decide)), h4.s0]; exact h4.dst ho
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L (o := 112) (.inr rfl) oa.env h28 hR oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hs₄.of_eq rd₅ wr₅ sp₅) dat₅)) fun s₆ ⟨ot, rd₆, wr₆, sp₆⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.s1, h4.s0] at f₆
  have F₆ : Frame (wF W s₀.sp) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .s8 = BitVec.ofNat 64 TL := h19
  have hTr : Covers [⟨s₄.gpr .s9, TL⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.s9]; exact h.tag
  have hTd : (⟨s₄.gpr .s9, TL⟩ : Region).Disjoint ⟨s₄.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.s9, h4.s0]; exact h.dtW.sub_right (Lay.wSub (by decide))
  have wa₄ : (s₄.gpr .s0).toNat % 8 = 0 := by rw [h4.s0]; exact wa
  refine WP.seq (WP.mono (recv_ok ot.env wa₄ h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  have he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.s0] at hf₇ hb₇
  have F₇ : Frame (wF W s₀.sp) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ wa₄ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  have he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.s0] at hf₈ h3₈
  have F₈ : Frame (wF W s₀.sp) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat
  let a := bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat
  let tg := bytesAt s₀.mem T TL
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
  let H := ctxH s₀.mem (s₀.gpr .a0)
  have hH₄ : blockAt s₄.mem (s₄.gpr .s2 + BitVec.ofNat 64 240) = H := by
    rw [h4.s2]; exact ctxH_keep F₄ dcF
  have iv₄ : bytesAt s₄.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat = iv :=
    bytes_W F₄ h.dnW (h.bufs _ (by simp)) (by have := (s₀.gpr .a3).isLt; omega_arith)
  have a₄ : bytesAt s₄.mem (s₀.gpr .a4) (s₄.gpr .s10).toNat = a := by
    rw [h4.s10]; exact bytes_W F₄ h.daW (h.bufs _ (by simp)) (by have := (s₀.gpr .a5).isLt; omega_arith)
  have ct₅ : bytesAt s₅.mem (s₀.gpr .a6) (s₄.gpr .s11).toNat = ct := by
    rw [h4.s11]; exact bytes_W F₅ h.dsW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  have hc₅ : ciphOf s₅.mem (s₄.gpr .s2) (s₀.gpr .a1).toNat = ciph := by rw [h4.s2]; exact ciph_keep F₅ dcF hR
  have hj₅ : blockAt s₅.mem (s₄.gpr .s1) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  have hT₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.s0, hc₅, hj₅, ct₅, ← h4.s0, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.s0]; exact ho
  have hT₇ : bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  have hr₇ : bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - TL) := by
    rw [hb₇, h4.s9]; congr 1; exact bytes_W F₆ h.dtW (h.bufs _ (by simp)) (by omega_arith)
  let X := (fullTag ciph H iv a ct).take TL = tg
  have hX : (bytesAt s₇.mem (W + BitVec.ofNat 64 112) TL ++
      zeros (16 - TL) = bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  have r3₈ : s₈.gpr .a0 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  have f₆₈ : Frame (otFrame (W + BitVec.ofNat 64 16) W 112 s₀.sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
    ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
  have cb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame f₆₈ (cb_ot L₀ hk₀), ← h4.s1, oa.cb, hH₄, iv₄]
  have dat₈ : s₈.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep f₆₈ (slot_ot L₀ hk₀ (by decide)), ← h4.s0]; exact dat₅
  have dst₈ : o = true → s₈.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6 := fun ho => by
    rw [slot_keep f₆₈ (slot_ot L₀ hk₀ (by decide))]; exact dst₅ ho
  have sv₈ : SavedAt s₈.mem W s₀ :=
    (((h4.saved.frame f₅ (saved_j0Frame L₀ hk₀)).frame f₆ (saved_otFrame L₀ hk₀ (.inr rfl))).frame hf₇
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame
      hf₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `s8`, and out of place the distance into `s9`
  refine WP.seq (WP.block_append (Steps.wp_mv fun s₉ u₉ => WP.block_nil ?_))
  have k₉ : Keeps s₈ s₉ := ⟨u₉.mem, u₉.rd, u₉.wr, u₉.sp⟩
  have g₉0 : s₉.gpr .s0 = W := by rw [u₉.other _ (by decide), he₈.fr _ (by decide), h4.s0]
  refine WP.mono (deltaArg_ok (o := o) (δ := Dst - s₀.gpr .a6) g₉0 wa (by
      rw [k₉.rd, k₉.wr, k₈.rd, k₈.wr, k₇.rd, k₇.wr, rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr]
      exact in_left (covers_off h.w (show dstO + 8 ≤ 2560 by decide) (by decide) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩))
      (fun ho => by rw [k₉.mem]; exact dst₈ ho)) fun s₁₀ ⟨d₁₀, g₁₀, k₁₀⟩ => ?_
  have kk : Keeps s₈ s₁₀ := k₉.trans k₁₀
  have g : ∀ r, r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s₈.gpr r := fun r h8 h9 => by
    rw [g₁₀ r h9, u₉.other r h8]
  have he₁₀ : Env s₁₀.gpr s₀.sp s₁₀ := he₈.self' (g _ (by decide) (by decide)) (g _ (by decide) (by decide))
    (g _ (by decide) (by decide)) kk
  have e : ∀ r ∈ frozen, r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s₄.gpr r := fun r hf h8 h9 =>
    (g r h8 h9).trans (he₈.fr r hf)
  have rd₁₀ : s₁₀.rd = s₄.rd := kk.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans rd₅)))
  have wr₁₀ : s₁₀.wr = s₄.wr := kk.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans wr₅)))
  refine k s₁₀ ⟨he₁₀, e, rd₁₀, wr₁₀, kk.mem ▸ sv₈, kk.mem ▸ F₈, by rw [kk.mem]; exact cb₈,
    by rw [kk.mem]; exact dat₈, fun ho => by rw [kk.mem]; exact dst₈ ho, ?_, d₁₀⟩
  rw [g₁₀ _ (by decide), u₉.gpr, r3₈]
  show _ = BitVec.ofNat 64 (if X then 1 else 0)
  by_cases hx : X
  · simp only [eq_true hx, ite_true]; rfl
  · simp only [eq_false hx, ite_false]; rfl

/-- What `open`'s body leaves before its end (`openFin`): the result in `a0`
and the plaintext at `Dst`; in place, the data as it was if the tag is
wrong. -/
structure BodyOut (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) (s : State) : Prop where
  s0 : s.gpr .s0 = W
  s11 : s.gpr .s11 = s₀.gpr .a7
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem W s₀
  dat : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  a0 : s.gpr .a0 = BitVec.ofNat 64 (if OpenTagOk s₀ T TL then 1 else 0)
  good : OpenTagOk s₀ T TL → bytesAt s.mem Dst (s₀.gpr .a7).toNat =
    gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
      (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
      (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)
  bad : ¬OpenTagOk s₀ T TL → o = false → bytesAt s.mem Dst (s₀.gpr .a7).toNat =
    bytesAt s₀.mem Dst (s₀.gpr .a7).toNat

/-- `open`'s body from the comparison's result on. -/
theorem open_tail {o : Bool} {s₀ s₄ s₉ : State} {W T Dst : Addr} {TL : Nat} (h : OPre o s₀ W T Dst TL)
    (h4 : SO2 o W T Dst s₀ s₄) (om : OpenMid o s₀ W T Dst TL s₄ s₉) :
    WP isa (.seq (.ite (.zero .s8) (.block []) (oneCryptWith o)) (.block [mov .a0 .s8])) s₉
      (BodyOut o s₀ W T Dst TL) := by
  have L₀ := h.lay
  have hk₀ := h.stk
  have hR := h.rounds
  have hk₄ := h4.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have dcF : ∀ r ∈ wF W s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dcW
    · exact hk₀.c
  have h28 : s₄.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h4.s3]; exact toN
  let iv := bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
  let H := ctxH s₀.mem (s₀.gpr .a0)
  have he₉ := om.env
  have e := om.regs
  have rd₉ := om.rd
  have wr₉ := om.wr
  have sv₉ := om.saved
  have F₉ := om.frame
  have sp₉ : s₉.sp = s₄.sp := he₉.sp.trans hk₄.sp.symm
  have src₉ : bytesAt s₉.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = ct :=
    bytes_W F₉ h.dsW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  have dst₉ : bytesAt s₉.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat :=
    bytes_W F₉ h.dDW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  have hk₉ : Keeps' s₀ s₉ := ⟨rd₉.trans hk₄.rd, wr₉.trans hk₄.wr, sp₉.trans hk₄.sp⟩
  have hd₉₀ : DataW (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₉ Dst (s₀.gpr .a7).toNat :=
    h.ddst.of_eq hk₉.rd hk₉.wr hk₉.sp
  have hs₉₀ : DataOk (W + BitVec.ofNat 64 16) W s₉ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    h.dsrc.of_eq hk₉.rd hk₉.wr hk₉.sp
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite (.zero .s8) (.block []) (oneCryptWith o)) s₉ fun s₁₀ =>
      (∀ r ∈ frozen, r ≠ .s9 → s₁₀.gpr r = s₉.gpr r) ∧ s₁₀.sp = s₉.sp ∧ SavedAt s₁₀.mem W s₀ ∧
      s₁₀.rd = s₄.rd ∧ s₁₀.wr = s₄.wr ∧
      s₁₀.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 ∧
      (o = true → s₁₀.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6) ∧
      ((OpenTagOk s₀ T TL) → bytesAt s₁₀.mem Dst (s₀.gpr .a7).toNat = gctr ciph (inc32 (j0 H iv)) ct) ∧
      (¬(OpenTagOk s₀ T TL) → bytesAt s₁₀.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat) := by
    refine WP.ite _ (eval_zero om.s8 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬(OpenTagOk s₀ T TL) := fun x => by simp [x] at ht
      exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, sv₉, rd₉, wr₉, om.dat, om.dst, fun x => absurd x hx,
        fun _ => dst₉⟩
    · have hx : (OpenTagOk s₀ T TL) := Classical.byContradiction fun x => by simp [x] at hf
      have L₉ : Lay (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) := by
        rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide), h4.s2, h4.s1, h4.s0]
        exact L₀
      have e11 : s₉.gpr .s11 = s₀.gpr .a7 := by rw [e _ (by decide) (by decide) (by decide), h4.s11]
      have hd₉ : DataW (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) s₉ Dst (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide), e11, h4.s2, h4.s1, h4.s0]
        exact hd₉₀
      have hs₉ : DataOk (s₉.gpr .s1) (s₉.gpr .s0) s₉ (s₀.gpr .a6) (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide), e11, h4.s1, h4.s0]
        exact hs₉₀
      have h28₉ : s₉.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by
        rw [e _ (by decide) (by decide) (by decide)]; exact h28
      have cb₉ : blockAt s₉.mem (s₉.gpr .s1 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide) (by decide), h4.s1]; exact om.cb
      have ds₉ : s₉.mem.readW (s₉.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
        rw [e _ (by decide) (by decide) (by decide), h4.s0]; exact om.dat
      refine WP.mono (WP.with_rdwr (oneCryptWith_ok L₉ he₉ h28₉ hR hd₉ hs₉ (by rw [e11]; exact h.alias)
        om.s9 ds₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
        e11, h4.s1, h4.s0] at cf
      have dS : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 256 → s₁₀.mem.readW (W + BitVec.ofNat 64 d) 64 =
          s₉.mem.readW (W + BitVec.ofNat 64 d) 64 := fun hd =>
        slot_keep cf (slot_crFrame' (V := fun r => if r = .s2 then s₀.gpr .a0 else if r = .s1 then
          W + BitVec.ofNat 64 16 else W) L₀ hd₉₀ hd)
      refine ⟨fun r hr _ => oc.env.fr r hr, oc.env.sp.trans he₉.sp.symm, sv₉.frame cf (saved_crFrame L₀ hd₉₀), rd₁₀.trans rd₉,
        wr₁₀.trans wr₉, by rw [dS (by decide)]; exact om.dat, fun ho => by rw [dS (by decide)]; exact om.dst ho,
        fun _ => ?_, fun x => absurd hx x⟩
      have ho := oc.out
      rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide), h4.s11, h4.s2,
        ciph_keep F₉ dcF hR, src₉] at ho
      exact ho
  refine WP.seq (WP.mono mid fun s₁₀ ⟨g₁₀, sp₁₀, sv₁₀, rd₁₀, wr₁₀, dat₁₀, dst₁₀, hd₁, hd₂⟩ => ?_)
  -- the result back into `a0`
  refine Steps.wp_mv fun s₁₁ u₁₁ => WP.block_nil ?_
  refine ⟨by rw [u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide), he₉.fr _ (by decide),
      e _ (by decide) (by decide) (by decide), h4.s0],
    by rw [u₁₁.other _ (by decide), g₁₀ _ (by decide) (by decide), he₉.fr _ (by decide),
      e _ (by decide) (by decide) (by decide), h4.s11],
    by rw [u₁₁.sp, sp₁₀, sp₉, hk₄.sp], by rw [u₁₁.rd, rd₁₀, hk₄.rd], by rw [u₁₁.wr, wr₁₀, hk₄.wr],
    by rw [u₁₁.mem]; exact sv₁₀, by rw [u₁₁.mem]; exact dat₁₀, fun ho => by rw [u₁₁.mem]; exact dst₁₀ ho,
    by rw [u₁₁.gpr, g₁₀ _ (by decide) (by decide), he₉.fr _ (by decide), om.s8],
    fun hx => by rw [u₁₁.mem]; exact hd₁ hx, fun hx _ => by rw [u₁₁.mem]; exact hd₂ hx⟩

/-- `open`'s body once the tag length is allowed. -/
theorem open_good [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Bool} {s₀ s₄ : State} {W T Dst : Addr} {TL : Nat}
    (h : OPre o s₀ W T Dst TL) (h4 : SO2 o W T Dst s₀ s₄)
    (h19 : s₄.gpr .s8 = BitVec.ofNat 64 TL) (hok : Spec.Gcm.tagLenOk TL = true) :
    WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block ([mov .s8 .a0] ++ deltaArg o))
      (.seq (.ite (.zero .s8) (.block []) (oneCryptWith o)) (.block [mov .a0 .s8]))))))) s₄
      (BodyOut o s₀ W T Dst TL) :=
  open_head h h4 h19 hok fun _ om => open_tail h h4 om

/-- What `open`'s body leaves for its end (`openFin`): the result in `a0`, 0
if the tag length `TL` is not allowed or the tag is wrong, and then (in
place) the data as it was; otherwise 1 and the plaintext at `Dst`. -/
structure BodyRes (o : Bool) (s₀ : State) (W T Dst : Addr) (TL : Nat) (s : State) : Prop where
  s0 : s.gpr .s0 = W
  s11 : s.gpr .s11 = s₀.gpr .a7
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : SavedAt s.mem W s₀
  dat : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6
  dst : o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6
  good : Spec.Gcm.tagLenOk TL = true ∧ OpenTagOk s₀ T TL →
    s.gpr .a0 = 1 ∧ bytesAt s.mem Dst (s₀.gpr .a7).toNat =
      gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)
  bad : ¬(Spec.Gcm.tagLenOk TL = true ∧ OpenTagOk s₀ T TL) →
    s.gpr .a0 = 0 ∧ (o = false → bytesAt s.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat)

/-- `open`'s body after the entry, with the tag length `TL` in `s8`, then `F`. -/
theorem open_body [VG.Proof.Gcm.RISCV64.GhashLaw] {o : Bool} {s₀ s₂ : State} {W T Dst : Addr} {TL : Nat}
    (h : OPre o s₀ W T Dst TL) (h2 : SO2 o W T Dst s₀ s₂) (h19 : s₂.gpr .s8 = BitVec.ofNat 64 TL)
    {F : Prog isa} {Q : State → Prop} (k : ∀ s, BodyRes o s₀ W T Dst TL s → WP isa F s Q) :
    WP isa (.seq tagLenOk (.seq (.ite (.zero .s5) (.block [.li .a0 0]) (openGoodWith o)) F)) s₂ Q := by
  have F₂ : Frame (wF W s₀.sp) s₀.mem s₂.mem := h2.frame
  refine WP.seq (WP.mono (tagLenOk_ok h19 h.tl) fun s₃ ⟨h25, g₃, k₃⟩ => ?_)
  refine WP.seq (WP.mono (Q := BodyRes o s₀ W T Dst TL) ?_ k)
  refine WP.ite _ (eval_zero h25 (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
  · have hbad : Spec.Gcm.tagLenOk TL = false := by
      cases e : Spec.Gcm.tagLenOk TL
      · rfl
      · simp [e] at ht
    refine Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.s0
    · rw [u.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h2.s11
    · rw [u.sp, k₃.sp]; exact h2.keeps.sp
    · rw [u.rd, k₃.rd]; exact h2.keeps.rd
    · rw [u.wr, k₃.wr]; exact h2.keeps.wr
    · rw [u.mem, k₃.mem]; exact h2.saved
    · rw [u.mem, k₃.mem]; exact h2.dat
    · intro ho; rw [u.mem, k₃.mem]; exact h2.dst ho
    · intro hx; rw [hbad] at hx; exact absurd hx.1 (by decide)
    · intro _; refine ⟨u.gpr, fun _ => ?_⟩
      rw [u.mem, k₃.mem]
      exact bytes_W F₂ h.dDW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  · have hok : Spec.Gcm.tagLenOk TL = true := by
      cases e : Spec.Gcm.tagLenOk TL
      · simp [e] at hf
      · rfl
    refine WP.seq (Steps.wp_mv fun s₄ u₄ => WP.block_nil ?_)
    have g₄ : ∀ r, r ≠ .t0 → r ≠ .s8 → s₄.gpr r = s₂.gpr r := fun r h0 h8 => by
      by_cases e : r = .s5
      · subst e
        rw [u₄.gpr, g₃ _ (by decide) (by decide), h2.s7, h2.s5]
      · rw [u₄.other r e, g₃ r h0 e]
    have h4 : SO2 o W T Dst s₀ s₄ :=
      h2.keep g₄ ⟨by rw [u₄.mem, k₃.mem], by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.sp, k₃.sp]⟩
    refine WP.mono (open_good h h4 (by rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide)]; exact h19) hok)
      fun s bo => ⟨bo.s0, bo.s11, bo.sp, bo.rd, bo.wr, bo.saved, bo.dat, bo.dst, fun hx => ⟨?_, bo.good hx.2⟩,
        fun hx => ⟨?_, bo.bad (fun x => hx ⟨hok, x⟩)⟩⟩
    · rw [bo.a0, ite_eq_left_of_eq_true _ _ (eq_true hx.2)]; rfl
    · rw [bo.a0, ite_eq_right_of_eq_false _ _ (eq_false (fun x => hx ⟨hok, x⟩))]; rfl

/-- The contract's postcondition, from `OpenPost`, through `restore`. -/
theorem openPost_out {s₀ s s' : State} (op : OpenPost s₀ s) (hm : s'.mem = s.mem) (h3 : s'.gpr .a0 = s.gpr .a0) :
    openRISCV64.post s₀ s' := by
  unfold OpenPost at op
  unfold openRISCV64
  dsimp only
  rw [hm, h3]
  split <;> rename_i heq <;> rw [heq] at op <;> exact ⟨by rw [op.1]; rfl, op.2⟩

/-- After a step that changes no register the entry set but `t0` and `s8`. -/
theorem SO1.keep {W T : Addr} {s₀ s₁ s₂ : State} (h1 : SO1 W T s₀ s₁)
    (hg : ∀ r, r ≠ .t0 → r ≠ .s8 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 W T s₀ s₂ :=
  ⟨⟨hk.rd.trans h1.keeps.rd, hk.wr.trans h1.keeps.wr, hk.sp.trans h1.keeps.sp⟩, hk.mem ▸ h1.saved,
    hk.mem ▸ h1.frame, hk.mem ▸ h1.aad, hk.mem ▸ h1.dat,
    by rw [hg _ (by decide) (by decide)]; exact h1.s0, by rw [hg _ (by decide) (by decide)]; exact h1.s1,
    by rw [hg _ (by decide) (by decide)]; exact h1.s2, by rw [hg _ (by decide) (by decide)]; exact h1.s3,
    by rw [hg _ (by decide) (by decide)]; exact h1.s4, by rw [hg _ (by decide) (by decide)]; exact h1.s5,
    by rw [hg _ (by decide) (by decide)]; exact h1.s7, by rw [hg _ (by decide) (by decide)]; exact h1.s10,
    by rw [hg _ (by decide) (by decide)]; exact h1.s11, by rw [hg _ (by decide) (by decide)]; exact h1.s9,
    by rw [hg _ (by decide) (by decide)]; exact h1.t1⟩

/-- The entry of `open`, and `tag_len` in `s8`. -/
theorem openEntry_wp {s₀ : State} (h : openPre s₀) :
    WP isa (.block openEntry) s₀ fun s₂ =>
      SO1 (stackArg s₀ 2) (stackArg s₀ 0) s₀ s₂ ∧ s₂.gpr .s8 = stackArg s₀ 1 := by
  have wa := h.opre.wa
  have hh := h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, -, hstk,
    -⟩ := hh
  have hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dA : (args s₀ 3).Disjoint (oneR (stackArg s₀ 2)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  have hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 2)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))
  have hLd : (⟨s₀.sp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 2)) := by
    have hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 0) (d := 8) (n := 8) (k := 24) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 16) (W := stackArg s₀ 2) (T := stackArg s₀ 0)
    (.inr rfl) hW wa hstk.1 (args_in hA (by decide) (i := 2) (by decide)) rfl
    (args_in hA (by decide) (i := 0) (by decide)) rfl hTd) fun s₁ h1 => ?_)
  -- `tag_len` into `s8`
  have hi : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 8) 8 := by
    rw [h1.keeps.rd, h1.keeps.wr]; exact args_in hA (by decide) (i := 1) (by decide)
  have hv : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = stackArg s₀ 1 := by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine Steps.wp_ld (off := 8) (a := s₀.sp + BitVec.ofNat 64 8) (by decide) (by rw [h1.t1])
    (Spill.al8 (by have := hstk.1; omega) (by decide)) hi fun s₂ u₂ => WP.block_nil ?_
  exact ⟨h1.keep (fun r _ hr => u₂.other r hr) ⟨u₂.mem, u₂.rd, u₂.wr, u₂.sp⟩, by rw [u₂.gpr, hv]⟩

theorem open_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s₀ : State} (h : openRISCV64.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openRISCV64.post s₀ s' := by
  have h' : openPre s₀ := h
  have hp := h'.opre
  have hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := hp.w
  refine WP.seq (WP.mono (openEntry_wp h') fun s₂ ⟨h2, h19⟩ => ?_)
  refine open_body hp h2.so2 (by rw [h19]; simp) fun s₅ ⟨h31, _, hsp, hrd, hwr, hsv, _, _, hg, hb⟩ => ?_
  show WP isa (.block restore) s₅ _
  refine WP.mono (restore_ok h31 hp.wa (by rw [hrd, hwr]; exact Covers.right hW) hsv hsp)
    fun s' ⟨ga, hm, h3, _⟩ => ⟨ga, openPost_out ?_ hm h3⟩
  have hres : openRes s₀ = if Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true ∧ openTagOk s₀ then
      some (gctr (ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat)
        (inc32 (j0 (ctxH s₀.mem (s₀.gpr .a0)) (bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat)))
        (bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat)) else none := by
    simp only [openRes, openResult, decryptWith]
    by_cases hl : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true
    · simp only [hl, ite_true, true_and]
    · simp only [hl, false_and, ite_false, Bool.false_eq_true]
  by_cases hx : Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true ∧ openTagOk s₀
  · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true hx))) (hg hx).1 (hg hx).2
  · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false hx))) (hb hx).1 ((hb hx).2 rfl)

end VG.Proof.AesGcm.RISCV64
