module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTText
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTJ0
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamInit
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Fn
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
meta import VerifiedGarbage.Proof.Gcm.Compose
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.RISCV64
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamFinish
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneEntry
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-! ### `AesGcm.RISCV64.CTOpen`, which this module and modules that import it used -/

section

/-! ### `AesGcm.RISCV64.Open`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTCrypt.lean`): `open` checks the tag length; if it is
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
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega_using [hd], by omega_using [hd]⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega_using [hd]))
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)

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
  obtain mr : ∀ {r : Region}, r ∈ s₀.rd → Covers [r] (s₀.rd ++ s₀.wr) := fun h =>
    covers_mem (List.mem_append_left _ h)
  obtain hD : Covers [⟨s₀.gpr .a6, (s₀.gpr .a7).toNat⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
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
  obtain perm : Perm (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₁ :=
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
  obtain he₄ := h4.env h.ctx h.w hk₀
  obtain L := L₀.v h4.s2 h4.s1 h4.s0
  have hk₄ := h4.keeps
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ wF W s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dcW
    · exact hk₀.c
  have F₄ : Frame (wF W s₀.sp) s₀.mem s₄.mem := h4.frame
  -- `oneAad`
  obtain hN : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a2) (s₀.gpr .a3).toNat := by
    rw [h4.s1, h4.s0]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.nonce, (s₀.gpr .a3).isLt, h.fn, h.dnW.sub_right (Lay.wSub (by decide)),
      h.dnW, by rw [hk₄.sp]; exact h.bufs _ (by simp)⟩
  obtain hAd : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a4) (s₄.gpr .s10).toNat := by
    rw [h4.s1, h4.s0, h4.s10]
    exact ⟨by rw [hk₄.rd, hk₄.wr]; exact h.aad, (s₀.gpr .a5).isLt, h.fa, h.daW.sub_right (Lay.wSub (by decide)),
      h.daW, by rw [hk₄.sp]; exact h.bufs _ (by simp)⟩
  refine WP.seq (WP.mono (WP.with_rdwr (oneAad_ok L he₄ rfl h4.s4 (by rw [h4.s5]; exact toN)
    (by rw [h4.s7]; exact toN) hN hAd (by rw [h4.s0]; exact h4.aad))) fun s₅ ⟨oa, rd₅, wr₅, sp₅⟩ => ?_)
  have f₅ := oa.frame
  rw [h4.s1, h4.s0] at f₅
  obtain F₅ : Frame (wF W s₀.sp) s₀.mem s₅.mem := F₄.trans (f₅.sub inW_j0)
  -- `oneTag 112`
  obtain hs₄ : DataOk (s₄.gpr .s1) (s₄.gpr .s0) s₄ (s₀.gpr .a6) (s₄.gpr .s11).toNat := by
    rw [h4.s1, h4.s0, h4.s11]; exact h.dsrc.of_eq hk₄.rd hk₄.wr hk₄.sp
  obtain h28 : s₄.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h4.s3]; exact toN
  obtain dat₅ : s₅.mem.readW (s₄.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep oa.frame (slot_j0 L he₄.stk' (by decide)), h4.s0]; exact h4.dat
  obtain dst₅ : o = true → s₅.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6 := fun ho => by
    rw [← h4.s0, slot_keep oa.frame (slot_j0' L he₄.stk' (d := dstO) (by decide)), h4.s0]; exact h4.dst ho
  refine WP.seq (WP.mono (WP.with_rdwr (oneTag_ok L (o := 112) (.inr rfl) oa.env h28 hR oa.hH
    (length_bytesAt _ _ _).symm oa.abs (hs₄.of_eq rd₅ wr₅ sp₅) dat₅)) fun s₆ ⟨ot, rd₆, wr₆, sp₆⟩ => ?_)
  have f₆ := ot.frame
  rw [h4.s1, h4.s0] at f₆
  obtain F₆ : Frame (wF W s₀.sp) s₀.mem s₆.mem := F₅.trans (f₆.sub inW_ot)
  -- `recv`
  have h19' : s₄.gpr .s8 = BitVec.ofNat 64 TL := h19
  obtain hTr : Covers [⟨s₄.gpr .s9, TL⟩] (s₆.rd ++ s₆.wr) := by
    rw [rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr, h4.s9]; exact h.tag
  obtain hTd : (⟨s₄.gpr .s9, TL⟩ : Region).Disjoint ⟨s₄.gpr .s0 + BitVec.ofNat 64 256, 16⟩ := by
    rw [h4.s9, h4.s0]; exact h.dtW.sub_right (Lay.wSub (by decide))
  obtain wa₄ : (s₄.gpr .s0).toNat % 8 = 0 := by rw [h4.s0]; exact wa
  refine WP.seq (WP.mono (recv_ok ot.env wa₄ h19' t1 t16 hTr hTd) fun s₇ ⟨hb₇, hf₇, g₇, k₇⟩ => ?_)
  obtain he₇ := ot.env.keep (fun r hr => g₇ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₇.sp k₇.rd k₇.wr
  rw [h4.s0] at hf₇ hb₇
  obtain F₇ : Frame (wF W s₀.sp) s₀.mem s₇.mem := F₆.trans (hf₇.sub (inW_at (by decide)))
  -- `cmp 112`
  refine WP.seq (WP.mono (cmp_ok he₇ wa₄ (o := 112) (.inr rfl) h19' t1 t16) fun s₈ ⟨h3₈, hf₈, g₈, k₈⟩ => ?_)
  obtain he₈ := he₇.keep (fun r hr => g₈ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) k₈.sp k₈.rd k₈.wr
  rw [h4.s0] at hf₈ h3₈
  obtain F₈ : Frame (wF W s₀.sp) s₀.mem s₈.mem := F₇.trans (hf₈.sub (inW_at (by decide)))
  -- what the tags are
  let iv := bytesAt s₀.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat
  let a := bytesAt s₀.mem (s₀.gpr .a4) (s₀.gpr .a5).toNat
  let ct := bytesAt s₀.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat
  let tg := bytesAt s₀.mem T TL
  let ciph := ctxCiph s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat
  let H := ctxH s₀.mem (s₀.gpr .a0)
  obtain hH₄ : blockAt s₄.mem (s₄.gpr .s2 + BitVec.ofNat 64 240) = H := by
    rw [h4.s2]; exact ctxH_keep F₄ dcF
  obtain iv₄ : bytesAt s₄.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat = iv :=
    bytes_W F₄ h.dnW (h.bufs _ (by simp)) (by have := (s₀.gpr .a3).isLt; omega_arith)
  obtain a₄ : bytesAt s₄.mem (s₀.gpr .a4) (s₄.gpr .s10).toNat = a := by
    rw [h4.s10]; exact bytes_W F₄ h.daW (h.bufs _ (by simp)) (by have := (s₀.gpr .a5).isLt; omega_arith)
  obtain ct₅ : bytesAt s₅.mem (s₀.gpr .a6) (s₄.gpr .s11).toNat = ct := by
    rw [h4.s11]; exact bytes_W F₅ h.dsW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  obtain hc₅ : ciphOf s₅.mem (s₄.gpr .s2) (s₀.gpr .a1).toNat = ciph := by rw [h4.s2]; exact ciph_keep F₅ dcF hR
  obtain hj₅ : blockAt s₅.mem (s₄.gpr .s1) = j0 H iv := by rw [oa.j, hH₄, iv₄]
  obtain hT₆ : bytesAt s₆.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    have ho := ot.out
    rw [h4.s0, hc₅, hj₅, ct₅, ← h4.s0, hH₄, a₄, ← Proof.Gcm.fullTag_eq] at ho
    rw [← h4.s0]; exact ho
  obtain hT₇ : bytesAt s₇.mem (W + BitVec.ofNat 64 112) 16 = fullTag ciph H iv a ct := by
    rw [bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)]
    exact hT₆
  obtain hr₇ : bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16 = tg ++ zeros (16 - TL) := by
    rw [hb₇, h4.s9]; congr 1; exact bytes_W F₆ h.dtW (h.bufs _ (by simp)) (by omega_arith)
  let X := (fullTag ciph H iv a ct).take TL = tg
  obtain hX : (bytesAt s₇.mem (W + BitVec.ofNat 64 112) TL ++
      zeros (16 - TL) = bytesAt s₇.mem (W + BitVec.ofNat 64 256) 16) ↔ X := by
    rw [bytesAt_take _ _ t16, hT₇, hr₇, List.append_cancel_right_eq]
  obtain r3₈ : s₈.gpr .a0 = if X then 1 else 0 := by
    rw [h3₈]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  obtain f₆₈ : Frame (otFrame (W + BitVec.ofNat 64 16) W 112 s₀.sp ++
      [⟨W + BitVec.ofNat 64 256, 16⟩, ⟨W + BitVec.ofNat 64 272, 16⟩]) s₅.mem s₈.mem :=
    ((f₆.mono fun r hr => List.mem_append_left _ hr).trans (hf₇.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)).trans (hf₈.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)
  obtain cb₈ : blockAt s₈.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    rw [blockAt_frame f₆₈ (cb_ot L₀ hk₀), ← h4.s1, oa.cb, hH₄, iv₄]
  obtain dat₈ : s₈.mem.readW (W + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
    rw [slot_keep f₆₈ (slot_ot L₀ hk₀ (by decide)), ← h4.s0]; exact dat₅
  obtain dst₈ : o = true → s₈.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - s₀.gpr .a6 := fun ho => by
    rw [slot_keep f₆₈ (slot_ot L₀ hk₀ (by decide))]; exact dst₅ ho
  obtain sv₈ : SavedAt s₈.mem W s₀ :=
    (((h4.saved.frame f₅ (saved_j0Frame L₀ hk₀)).frame f₆ (saved_otFrame L₀ hk₀ (.inr rfl))).frame hf₇
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))).frame
      hf₈ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact saved_w (by decide) (.inr (by decide)))
  -- the result into `s8`, and out of place the distance into `s9`
  refine WP.seq (WP.block_append (Steps.wp_mv fun s₉ u₉ => WP.block_nil ?_))
  obtain k₉ : Keeps s₈ s₉ := ⟨u₉.mem, u₉.rd, u₉.wr, u₉.sp⟩
  obtain g₉0 : s₉.gpr .s0 = W := by rw [u₉.other _ (by decide), he₈.fr _ (by decide), h4.s0]
  refine WP.mono (deltaArg_ok (o := o) (δ := Dst - s₀.gpr .a6) g₉0 wa (by
      rw [k₉.rd, k₉.wr, k₈.rd, k₈.wr, k₇.rd, k₇.wr, rd₆, wr₆, rd₅, wr₅, hk₄.rd, hk₄.wr]
      exact in_left (covers_off h.w (show dstO + 8 ≤ 2560 by decide) (by decide) _ _
        ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩))
      (fun ho => by rw [k₉.mem]; exact dst₈ ho)) fun s₁₀ ⟨d₁₀, g₁₀, k₁₀⟩ => ?_
  obtain kk : Keeps s₈ s₁₀ := k₉.trans k₁₀
  obtain g : ∀ r, r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s₈.gpr r := fun r h8 h9 => by
    rw [g₁₀ r h9, u₉.other r h8]
  obtain he₁₀ : Env s₁₀.gpr s₀.sp s₁₀ := he₈.self' (g _ (by decide) (by decide)) (g _ (by decide) (by decide))
    (g _ (by decide) (by decide)) kk
  obtain e : ∀ r ∈ frozen, r ≠ .s8 → r ≠ .s9 → s₁₀.gpr r = s₄.gpr r := fun r hf h8 h9 =>
    (g r h8 h9).trans (he₈.fr r hf)
  obtain rd₁₀ : s₁₀.rd = s₄.rd := kk.rd.trans (k₈.rd.trans (k₇.rd.trans (rd₆.trans rd₅)))
  obtain wr₁₀ : s₁₀.wr = s₄.wr := kk.wr.trans (k₈.wr.trans (k₇.wr.trans (wr₆.trans wr₅)))
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
  obtain toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  obtain dcF : ∀ r ∈ wF W s₀.sp, (⟨s₀.gpr .a0, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.dcW
    · exact hk₀.c
  obtain h28 : s₄.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by rw [h4.s3]; exact toN
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
  obtain sp₉ : s₉.sp = s₄.sp := he₉.sp.trans hk₄.sp.symm
  obtain src₉ : bytesAt s₉.mem (s₀.gpr .a6) (s₀.gpr .a7).toNat = ct :=
    bytes_W F₉ h.dsW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  obtain dst₉ : bytesAt s₉.mem Dst (s₀.gpr .a7).toNat = bytesAt s₀.mem Dst (s₀.gpr .a7).toNat :=
    bytes_W F₉ h.dDW (h.bufs _ (by simp)) (by have := (s₀.gpr .a7).isLt; omega_arith)
  obtain hk₉ : Keeps' s₀ s₉ := ⟨rd₉.trans hk₄.rd, wr₉.trans hk₄.wr, sp₉.trans hk₄.sp⟩
  obtain hd₉₀ : DataW (s₀.gpr .a0) (W + BitVec.ofNat 64 16) W s₉ Dst (s₀.gpr .a7).toNat :=
    h.ddst.of_eq hk₉.rd hk₉.wr hk₉.sp
  obtain hs₉₀ : DataOk (W + BitVec.ofNat 64 16) W s₉ (s₀.gpr .a6) (s₀.gpr .a7).toNat :=
    h.dsrc.of_eq hk₉.rd hk₉.wr hk₉.sp
  -- the data decrypted only if the tags are equal
  obtain mid : WP isa (.ite (.zero .s8) (.block []) (oneCryptWith o)) s₉ fun s₁₀ =>
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
      obtain L₉ : Lay (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) := by
        rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide), h4.s2, h4.s1, h4.s0]
        exact L₀
      obtain e11 : s₉.gpr .s11 = s₀.gpr .a7 := by rw [e _ (by decide) (by decide) (by decide), h4.s11]
      obtain hd₉ : DataW (s₉.gpr .s2) (s₉.gpr .s1) (s₉.gpr .s0) s₉ Dst (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
          e _ (by decide) (by decide) (by decide), e11, h4.s2, h4.s1, h4.s0]
        exact hd₉₀
      obtain hs₉ : DataOk (s₉.gpr .s1) (s₉.gpr .s0) s₉ (s₀.gpr .a6) (s₉.gpr .s11).toNat := by
        rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide), e11, h4.s1, h4.s0]
        exact hs₉₀
      obtain h28₉ : s₉.gpr .s3 = BitVec.ofNat 64 (s₀.gpr .a1).toNat := by
        rw [e _ (by decide) (by decide) (by decide)]; exact h28
      obtain cb₉ : blockAt s₉.mem (s₉.gpr .s1 + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
        rw [e _ (by decide) (by decide) (by decide), h4.s1]; exact om.cb
      obtain ds₉ : s₉.mem.readW (s₉.gpr .s0 + BitVec.ofNat 64 dataO) 64 = s₀.gpr .a6 := by
        rw [e _ (by decide) (by decide) (by decide), h4.s0]; exact om.dat
      refine WP.mono (WP.with_rdwr (oneCryptWith_ok L₉ he₉ h28₉ hR hd₉ hs₉ (by rw [e11]; exact h.alias)
        om.s9 ds₉ cb₉)) fun s₁₀ ⟨oc, rd₁₀, wr₁₀, _⟩ => ?_
      have cf := oc.frame
      rw [e _ (by decide) (by decide) (by decide), e _ (by decide) (by decide) (by decide),
        e11, h4.s1, h4.s0] at cf
      obtain dS : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 256 → s₁₀.mem.readW (W + BitVec.ofNat 64 d) 64 =
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
    obtain g₄ : ∀ r, r ≠ .t0 → r ≠ .s8 → s₄.gpr r = s₂.gpr r := fun r h0 h8 => by
      by_cases e : r = .s5
      · subst e
        rw [u₄.gpr, g₃ _ (by decide) (by decide), h2.s7, h2.s5]
      · rw [u₄.other r e, g₃ r h0 e]
    obtain h4 : SO2 o W T Dst s₀ s₄ :=
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
  obtain hW : Covers [⟨stackArg s₀ 2, 2560⟩] s₀.wr := by rw [hwr]; exact covers_mem (by simp)
  obtain hA : Covers [args s₀ 3] (s₀.rd ++ s₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dA : (args s₀ 3).Disjoint (oneR (stackArg s₀ 2)) :=
    (dWA.sub_left (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  obtain hTd : (⟨s₀.sp + BitVec.ofNat 64 0, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 2)) :=
    dA.sub_left (Region.sub_prefix (show 8 ≤ 8 * 3 by decide))
  obtain hLd : (⟨s₀.sp + BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (oneR (stackArg s₀ 2)) := by
    obtain hs := Offset.sub_base (s₀.sp + BitVec.ofNat 64 0) (d := 8) (n := 8) (k := 24) (by decide)
    rw [add_ofNat_assoc] at hs
    exact dA.sub_left hs
  unfold openEntry
  refine WP.block_append (WP.mono (one1_wp (off := 16) (W := stackArg s₀ 2) (T := stackArg s₀ 0)
    (.inr rfl) hW wa hstk.1 (args_in hA (by decide) (i := 2) (by decide)) rfl
    (args_in hA (by decide) (i := 0) (by decide)) rfl hTd) fun s₁ h1 => ?_)
  -- `tag_len` into `s8`
  obtain hi : InRegions (s₁.rd ++ s₁.wr) (s₀.sp + BitVec.ofNat 64 8) 8 := by
    rw [h1.keeps.rd, h1.keeps.wr]; exact args_in hA (by decide) (i := 1) (by decide)
  obtain hv : s₁.mem.readW (s₀.sp + BitVec.ofNat 64 8) 64 = stackArg s₀ 1 := by
    rw [Frame.readW h1.frame (r := ⟨s₀.sp + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hLd) (by decide)]
    rfl
  refine Steps.wp_ld (off := 8) (a := s₀.sp + BitVec.ofNat 64 8) (by decide) (by rw [h1.t1])
    (Spill.al8 (by have := hstk.1; omega_using [this]) (by decide)) hi fun s₂ u₂ => WP.block_nil ?_
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
  obtain hres : openRes s₀ = if Spec.Gcm.tagLenOk (stackArg s₀ 1).toNat = true ∧ openTagOk s₀ then
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

end

end

/-! ### `AesGcm.RISCV64.CTVerify`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/CTOpen.lean`): the invariant fixes what `finish`'s
does (`FinI`), and the received tag's address and length (`s9`, `s8`);
the branch on the tag length is on that public length, and the comparison
does not branch.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- In `verify`, after the entry: the received tag's `tl` bytes at `Tp`,
apart from `W`, which the state may read. -/
def VerI (c st w sp : Addr) (R : Nat) (A T Tp : BitVec 64) (tl : Nat) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s3 = BitVec.ofNat 64 R ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s9 = Tp ∧ V .s8 = BitVec.ofNat 64 tl ∧ Env V sp s ∧ Covers [⟨Tp, tl⟩] (s.rd ++ s.wr) ∧
    (⟨Tp, tl⟩ : Region).Disjoint ⟨w, 2560⟩

theorem verEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) (.block verEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem recv_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s0]) recv h).isSome =
    true := ⟨_, by taint_decide⟩

theorem cmp_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 0) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem li3_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block [.li .a0 0]) h).isSome =
    true := ⟨_, by taint_decide⟩

section
variable {c st w sp : Addr} (L : Lay c st w) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) {A T Tp : BitVec 64}
  {tl : Nat}
include L hR

/-- `verify` after the tag length is known to be allowed. -/
theorem verOk_ct [VG.Proof.Gcm.RISCV64.GhashLaw] (t1 : 1 ≤ tl) (t16 : tl ≤ 16) :
    CT (VerI c st w sp R A T Tp tl) (.seq recv (.seq (finTag 0) (cmp 0))) := by
  refine CT.seq (J := VerI c st w sp R A T Tp tl) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, i₁, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, i₂, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
    · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), i₁, i₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · refine WP.mono (recv_ok he (by rw [d]; exact L.wal) j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
      (by decide)))) fun s' ⟨_, _, hg, hk⟩ => ⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd⟩
  refine CT.seq (J := VerI c st w sp R A T Tp tl)
    ((finTag_ct L (o := 0) (.inl rfl) hR).mono fun s ⟨V, a, b, d, e, f, g, _, _, he, _⟩ =>
      ⟨V, a, b, d, e, f, g, he⟩)
    (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ => WP.mono (WP.with_rdwr (finTag_ok (L.v a b d) (o := 0)
      (.inl rfl) (a := List.replicate (A.toNat % 16) 0) (ct := List.replicate T.toNat 0) he e hR rfl
      (by simp [f]) (by simp [g]))) fun s' ⟨fo, rd, wr, _⟩ =>
        ⟨V, a, b, d, e, f, g, i, j, fo.env, by rw [rd, wr]; exact hT, hTd⟩) ?_
  obtain ⟨_, hc⟩ := cmp_taint
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, d₁, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, d₂, _, _, _, _, j₂, h₂, _⟩ =>
    ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · rw [h₁.s0, h₂.s0, d₁, d₂]

/-- The same, for correctness: `W` is kept in `s0`. -/
theorem verOk_wp [VG.Proof.Gcm.RISCV64.GhashLaw] (t1 : 1 ≤ tl) (t16 : tl ≤ 16) {s : State} (h : VerI c st w sp R A T Tp tl s) :
    WP isa (.seq recv (.seq (finTag 0) (cmp 0))) s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ := h
  refine WP.seq (WP.mono (recv_ok he (by rw [d]; exact L.wal) j t1 t16 (by rw [i]; exact hT) (by rw [i, d]; exact hTd.sub_right (Lay.wSub
    (by decide)))) fun s₁ ⟨_, _, hg, hk⟩ => ?_)
  have he₁ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) hk.sp hk.rd hk.wr
  refine WP.seq (WP.mono (finTag_ok (L.v a b d) (o := 0) (.inl rfl) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he₁ e hR rfl (by simp [f]) (by simp [g])) fun s₂ fo => ?_)
  refine WP.mono (cmp_ok fo.env (by rw [d]; exact L.wal) (o := 0) (.inl rfl) j t1 t16) fun s' ⟨_, _, hg', hk'⟩ =>
    ⟨by rw [hg' _ (by decide) (by decide) (by decide) (by decide) (by decide), fo.env.s0, d],
      by rw [hk'.sp, fo.env.sp]⟩

end

theorem streamVerify_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamVerifyRISCV64.pre streamVerifyRISCV64.pub streamVerify := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  have h₁' : verPre σ₁ := h₁
  have L := verLay h₁'
  have hR := ver_R h₁'
  let I₀ : State → Prop := fun s => verPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, q9.symm, q10.symm, qsp.symm⟩, ?_⟩
  let tl := (σ₁.gpr .a6).toNat
  let VI := VerI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a1).toNat (σ₁.gpr .a3) (σ₁.gpr .a4)
    (σ₁.gpr .a5) tl
  refine CT.seq (J := VI) ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := verEntry_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  · refine WP.mono (ver1_wp (ver_W hs) (ver_al hs)) fun s₁ h1 => ?_
    have hT : Covers [⟨s.gpr .a5, (s.gpr .a6).toNat⟩] (s₁.rd ++ s₁.wr) := by
      rw [h1.en.keeps.rd, h1.en.keeps.wr, hs.1]; exact covers_mem (List.mem_append_left _ (by simp))
    have hTd : (⟨s.gpr .a5, (s.gpr .a6).toNat⟩ : Region).Disjoint ⟨s.gpr .a7, 2560⟩ := hs.2.2.2.2.2.2.1
    refine ⟨s₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1.s2, e3]
    · rw [h1.s1, e5]
    · rw [h1.s0, e10]
    · rw [h1.s3, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [h1.s10, e6]
    · rw [h1.s11, e7]
    · rw [h1.s9, e8]
    · rw [h1.s8, e9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [← esp]; exact ver_env hs h1
    · simp only [tl]; rw [← e8, ← e9]; exact hT
    · simp only [tl]; rw [← e8, ← e9, ← e10]; exact hTd
  -- the tag length
  let ok := Spec.Gcm.tagLenOk tl
  let J : State → Prop := fun s => VI s ∧ s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J) ?_ (fun s ⟨V, a, b, d, e, f, g, i, j, he, hT, hTd⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, _, _, j₁, h₁, _⟩ ⟨_, _, _, _, _, _, _, _, j₂, h₂, _⟩ =>
      ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.fr _ (by decide), h₂.fr _ (by decide), j₁, j₂]
  · refine WP.mono (tagLenOk_ok (by rw [he.fr _ (by decide), j]) (σ₁.gpr .a6).isLt) fun s' ⟨h25, hg, hk⟩ =>
      ⟨⟨V, a, b, d, e, f, g, i, j, he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide))
        hk.sp hk.rd hk.wr, by rw [hk.rd, hk.wr]; exact hT, hTd⟩, h25⟩
  have ev : ∀ s, J s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s h => eval_zero h.2 (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp) ?_ (fun s hs => ?_) ?_
  · refine CT.ite _ ev (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨_, hc⟩ := li3_taint
      exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, _, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, _, _, _, _, _, h₂, _⟩, _⟩ =>
        ⟨h₁.sp.trans h₂.sp.symm, fun r hr => by simp at hr⟩) hc
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact (verOk_ct L hR t1 t16).mono fun s h => h.1
  · refine WP.ite _ (ev s hs) (fun hb => ?_) (fun hb => ?_)
    · obtain ⟨⟨V, _, _, d, _, _, _, _, _, he, _⟩, _⟩ := hs
      have h₀ : WP isa (.block [.li .a0 0]) s fun s' => (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
        crun [Int.reduceNatCast']
        exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
      exact WP.mono h₀ fun s' ⟨hg, hk⟩ => ⟨by rw [hg _ (by decide), he.s0, d], by rw [hk.sp, he.sp]⟩
    · have hok : ok = true := by cases e : ok <;> simp_all
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      exact verOk_wp L hR t1 t16 hs.1
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_open` is constant time

Untrusted: everything here is checked by Lean. The entry as for `seal`
(`CTSeal.lean`), then `tag_len` (`s8`), public, and the two branches of
`tagLenOk`. Once the tag length is allowed, the data is decrypted only if
the tags are equal, which may differ between two runs only as the result
does (the contract's `pub`: whether it succeeds). The invariants of the
pieces up to that comparison carry what the rest of each run reaches
(`CT.seqG`, from `open_head`): the result in `s8`, which is then the same in
both runs.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- Two runs of `c₁` carry what a further `R` reaches from them. -/
theorem CT.seqG {I J Z : State → Prop} {c₁ R c₂ : Prog isa} (h₁ : CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT (fun s => J s ∧ WP isa R s Z) c₂) : CT (fun s => I s ∧ WP isa (.seq c₁ R) s Z) (.seq c₁ c₂) :=
  CT.seq (h₁.mono fun _ h => h.1) (fun s h => WP.mono (WP.forall_det (w s h.1) (P := fun _ : Unit => True)
    (Q := fun _ s' => WP isa R s' Z) fun _ _ => WP.seq_iff.mp h.2) fun _ h => ⟨h.1, h.2 () trivial⟩) h₂

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 1).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (t.gpr .a0) (t.gpr .a1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .a0)) (bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat)))
        (bytesAt t.mem (t.gpr .a6) (t.gpr .a7).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 16]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1])
    (.block (oneRest ++ ([.load .d .s8 .t1 8] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint' : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp112_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 112) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem nil_taint (b : List Instr) (h : b = [.li .a0 0] ∨ b = [mov .s5 .s7] ∨ b = [mov .s8 .a0] ∨
    b = [mov .a0 .s8]) : ∃ hh, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block b) hh).isSome = true := by
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- Out of place, where `vg_aes_gcm_open_to` writes the data (`OD`) and the
distance to it at `W + dstO`. -/
def OX (o : Bool) (c W : Addr) (D Dst Ln : BitVec 64) (s : State) : Prop :=
  OD o c W D Dst Ln s ∧ (o = true → s.mem.readW (W + BitVec.ofNat 64 dstO) 64 = Dst - D)

/-- `OneI`, with the tag's address `T` and length `TL` in `s9` and `s8`, and
where the data goes (`OX`). -/
def OneO (o : Bool) (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T TL Dst : BitVec 64) (s : State) :
    Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ s.gpr .s8 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr) ∧
    OX o c W D Dst Ln s

section
variable {o : Bool} {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T TL Dst : BitVec 64}

theorem OX.frame {s s' : State} (h : OX o c W D Dst Ln s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 dstO, 8⟩ : Region).Disjoint r) : OX o c W D Dst Ln s' :=
  ⟨h.1.of_eq hrd hwr hsp, fun ho => (slot_keep hf hs).trans (h.2 ho)⟩

theorem OneO.frame {s s' : State} (h : OneO o c W sp R Np n Ad A D Ln T TL Dst s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 256 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneO o c W sp R Np n Ad A D Ln T TL Dst s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf (fun hd => hs ⟨hd.1, by omega_using [hd]⟩), (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2.1,
    h.2.2.2.2.frame hrd hwr hsp hf (hs (d := dstO) (by decide))⟩

/-- `OneI` after a step that changes only `s8` and `s9` among the registers it
pins. -/
theorem OneI.self {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s)
    (hg : ∀ r, r ≠ .s8 → r ≠ .s9 → s'.gpr r = s.gpr r) (hk : Keeps s s') : OneI c W sp R Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, r ≠ .s8 → r ≠ .s9 → s'.gpr r = V r := fun r hr h19 h20 =>
    (hg r h19 h20).trans (he.fr r hr)
  refine ⟨s'.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he.self' (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
    (hg _ (by decide) (by decide)) hk, hN.of_eq hk.rd hk.wr hk.sp,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩
  · rw [q _ (by decide) (by decide) (by decide), a]
  · rw [q _ (by decide) (by decide) (by decide), b]
  · rw [q _ (by decide) (by decide) (by decide), d]
  · rw [q _ (by decide) (by decide) (by decide), e]
  · rw [q _ (by decide) (by decide) (by decide), f]
  · rw [q _ (by decide) (by decide) (by decide), i]
  · rw [q _ (by decide) (by decide) (by decide), k]

/-- The result of the comparison in `s8`, for `b`. -/
abbrev Res (b : Bool) (s : State) : Prop := s.gpr .s8 = BitVec.ofNat 64 (if b then 1 else 0)

/-- The slots of the addresses are apart from what `oneTag 112` writes. -/
theorem slot_ot112 (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp) {d : Nat}
    (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega_using [hd], by omega_using [hd]⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega_using [hd]))

/-- The slots are apart from a block of `W` at `e ≥ 256`. -/
theorem slot_at {e : Nat} (he : 256 ≤ e) (he' : e + 16 ≤ 2560) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 256) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 e, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact Lay.w_w (.inl (by omega_using [he, hd])) (by omega_using [hd]) he'

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool)
include L hR hTd t1 t16

omit L hR hTd t1 t16 in
theorem deltaArg_taint (o : Bool) : ∃ hh, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s0])
    (.block ([mov .s8 .a0] ++ deltaArg o)) hh).isSome = true := by
  cases o <;> exact ⟨_, by taint_decide⟩

/-- `open`'s body from `oneAad` on, once the tag length is allowed, with what
the comparison of the tags gives (`Res b`); in place, or out of place to
`Dst`. -/
theorem openGood_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    CT (fun s => (OneO o c W sp R Np n Ad A D Ln T TL Dst s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n) ∧ WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112)
      (.seq (.block ([mov .s8 .a0] ++ deltaArg o)) (.block [])))))) s (Res b))
    (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block ([mov .s8 .a0] ++ deltaArg o))
      (.seq (.ite (.zero .s8) (.block []) (oneCryptWith o)) (.block [mov .a0 .s8]))))))) := by
  -- `oneAad`
  refine CT.seqG (J := fun s => OneO o c W sp R Np n Ad A D Ln T TL Dst s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0' (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneTag 112`
  refine CT.seqG (J := OneO o c W sp R Np n Ad A D Ln T TL Dst)
    ((oneTag_ct L (.inr rfl) hR).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have hk := he.stk'
    rw [a, b, d] at hk
    exact WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) (o := 112) (.inr rfl) (H := H) (a := x) (D := D) he e hR
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, rd, wr, sp'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) ot.env rd wr sp'
        (by have := ot.frame; rw [b, d] at this; exact this) (fun hd' => slot_ot112 L hk hd')
  -- `recv`
  refine CT.seqG (J := OneO o c W sp R Np n Ad A D Ln T TL Dst) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .s9 = T := by rw [← he.fr _ (by decide), hT.2.1]
    exact WP.mono (recv_ok he (by rw [d]; exact L.wal) h19 t1 t16 (by rw [h20]; exact hT.2.2.2.1)
      (by rw [h20, d]; exact hTd))
      fun s' ⟨_, hf', g', k'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
        (fun hd' => by rw [d]; exact slot_at (by decide) (by decide) hd')
  -- `cmp 112`
  refine CT.seqG (J := OneO o c W sp R Np n Ad A D Ln T TL Dst) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := cmp112_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, _, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, _, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b₁, b₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    exact WP.mono (cmp_ok he (by rw [d]; exact L.wal) (o := 112) (.inr rfl) h19 t1 t16)
      fun s' ⟨_, hf', g', k'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
        (fun hd' => by rw [d]; exact slot_at (by decide) (by decide) hd')
  -- the result into `s8`, and out of place the distance into `s9`
  refine CT.seqG (J := fun s => OneI c W sp R Np n Ad A D Ln s ∧ OD o c W D Dst Ln s ∧
    (o = true → s.gpr .s9 = Dst - D)) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := deltaArg_taint o
    exact CT.taintEq _ (fun _ => W) sp (fun s ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, _⟩ =>
      ⟨h₁.sp, by simp [h₁.s0, d₁]⟩) hc
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.block_append (Steps.wp_mv fun s₁ u₁ => WP.block_nil ?_)
    refine WP.mono (deltaArg_ok (o := o) (δ := Dst - D) (W := W)
      (by rw [u₁.other _ (by decide), he.s0, d]) L.wal
      (by rw [u₁.rd, u₁.wr]; exact in_left (he.perm.wC (show dstO + 8 ≤ 2560 by decide) _ _
        ⟨_, List.mem_singleton_self _, by rw [d]; exact Region.contains_self _ _⟩))
      (fun ho => by rw [u₁.mem]; exact hT.2.2.2.2.2 ho)) fun s' ⟨d', g', k'⟩ => ⟨?_, ?_, d'⟩
    · exact hT.1.self (fun r h8 h9 => by rw [g' r h9, u₁.other r h8])
        ⟨by rw [k'.mem, u₁.mem], by rw [k'.rd, u₁.rd], by rw [k'.wr, u₁.wr], by rw [k'.sp, u₁.sp]⟩
    · exact hT.2.2.2.2.1.of_eq (by rw [k'.rd, u₁.rd]) (by rw [k'.wr, u₁.wr]) (by rw [k'.sp, u₁.sp])
  -- the data decrypted only if the tags are equal, which both runs agree on
  have ev : ∀ s, (OneI c W sp R Np n Ad A D Ln s ∧ OD o c W D Dst Ln s ∧ (o = true → s.gpr .s9 = Dst - D)) ∧
      WP isa (.block []) s (Res b) → isa.eval (.zero .s8) s = some (decide ((if b then 1 else 0) = 0)) := fun s h =>
    eval_zero (WP.block_nil_iff.mp h.2) (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp)
    (CT.ite _ ev (fun _ => CT.skip) (fun _ => (oneCrypt_ct L hR).mono fun s h => h.1)) (fun s h => ?_) ?_
  · obtain ⟨V, a, b', d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h.1.1
    have hOD := h.1.2.1
    refine WP.ite _ (ev s h) (fun _ => WP.block_nil_iff.mpr ⟨by rw [he.s0, d], he.sp⟩) (fun _ => ?_)
    exact WP.mono (oneCryptWith_ok (L.v a b' d) he e hR (by rw [a, b', d, k]; exact hOD.1)
      (by rw [b', d, k]; exact hD) (by rw [k]; exact hOD.2)
      (fun ho => by rw [← he.fr .s9 (by decide)]; exact h.1.2.2 ho) (by rw [d]; exact sd) rfl)
      fun s' oc => ⟨by rw [oc.env.s0, d], oc.env.sp⟩
  · obtain ⟨_, hc⟩ := nil_taint [mov .a0 .s8] (.inr (.inr (.inr rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨_, hsp⟩ => ⟨hsp, by simp⟩) hc

end

/-- `mv s5, s7` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so1 {W T : Addr} {t₀ s₂ s₃ s₄ : State} (h2 : SO1 W T t₀ s₂)
    (g : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) (u : Steps.Upd s₃ s₄ .s5 (s₃.gpr .s7)) :
    SO1 W T t₀ s₄ ∧ s₄.gpr .s8 = s₂.gpr .s8 := by
  refine ⟨h2.keep (fun r h0 _ => ?_) ⟨by rw [u.mem, k.mem], by rw [u.rd, k.rd], by rw [u.wr, k.wr],
    by rw [u.sp, k.sp]⟩, by rw [u.other _ (by decide), g _ (by decide) (by decide)]⟩
  by_cases e : r = .s5
  · subst e
    rw [u.gpr, g _ (by decide) (by decide), h2.s7, h2.s5]
  · rw [u.other r e, g r h0 e]

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem open_one {t₀ s : State} (h : openPre t₀) (h1 : SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s)
    (h19 : s.gpr .s8 = stackArg t₀ 1) :
    OneO false (t₀.gpr .a0) (stackArg t₀ 2) t₀.sp (t₀.gpr .a1).toNat (t₀.gpr .a2) (t₀.gpr .a3).toNat (t₀.gpr .a4)
        (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 0) (stackArg t₀ 1) (t₀.gpr .a6) s ∧
      s.gpr .s4 = t₀.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a3).toNat := by
  have hk₀ := h.opre.stk
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hR, hstk,
    -⟩ := id h
  have hC : Covers [⟨t₀.gpr .a0, 256⟩] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg t₀ 2, 2560⟩] t₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨t₀.gpr .a6, (t₀.gpr .a7).toNat⟩] s.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  have hDok : DataOk (stackArg t₀ 2 + BitVec.ofNat 64 16) (stackArg t₀ 2) s (t₀.gpr .a6) (t₀.gpr .a7).toNat :=
    ⟨covers_left hDw, (t₀.gpr .a7).isLt, fd, ddW.sub_right (Lay.wSub (by decide)), ddW,
      by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  refine ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN, h1.s10, h1.s11,
    one_env h1 hC hW hk₀, ?_, ?_, hDok, h1.aad, h1.dat⟩, h1.s9, h19, ?_, ⟨⟨hDok, hDw, dcd⟩, rfl⟩, nofun⟩, h1.s4,
    by rw [h1.s5]; exact toN⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))

theorem open_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, hR, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => openPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qres hR).symm⟩, ?_⟩
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 1
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 2 else σ₁.gpr r
    have hl : openEntry = [.addSp .t1 0, .load .d .t1 .t1 16] ++ (oneRest ++ ([.load .d .s8 .t1 8] : List Instr)) := by
      rw [openEntry, oneEntry_eq, List.append_assoc]
    show CT I₀ (.block openEntry)
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, ea2, _⟩
      have hA : Covers [args s 3] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := hs.opre.al
      refine WP.mono (oneA_ok (W := stackArg s 2) (.inr rfl) hsa (args_in hA (by decide) (i := 2) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea2, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 1 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 1).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 1).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := oneLay fc fW dcW ca wa
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 2 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .a0 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .a2) (n := (σ₁.gpr .a3).toNat) (Ad := σ₁.gpr .a4) (A := σ₁.gpr .a5)
        (D := σ₁.gpr .a6) (Ln := σ₁.gpr .a7) (o := false) (Dst := σ₁.gpr .a6) L₀ hR (dtW.sub_right (Lay.wSub (by decide))) t1 t16
        (openRes σ₁).isSome)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      have o := open_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, ea2, esp] at o
      refine ⟨o, open_head hpre.opre h4.so2 (by rw [h19₄.trans h19]; simp) hok₀ (T' := .block [])
        fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8, ← eres, openRes_isSome hok₀]
      by_cases hx : openTagOk t₀
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩ := hs
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩)
      (fun ht => ?_) (fun hf => ?_)
    · exact Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil
        ⟨by rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea2],
          by rw [u.sp, k.sp, h1.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      exact WP.mono (open_good hpre.opre h4.so2 (by rw [h19₄.trans h19]; simp) hok₀) fun s' oo =>
        ⟨by rw [oo.s0, ea2], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 2) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.StreamCT`, which only this module used -/

section

/-! ### `AesGcm.RISCV64.StreamAad`, which this module and modules that import it used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers and sets up `absorb`'s arguments (`aadEntry_ok`); `absorb 16`
absorbs the data into the accumulator (`aad_run`), which keeps the rest of
the state (`streamAad_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom StreamRepr)
open VG.Proof.Gcm (Absorbed Ctr)

/-- The entry: `absorb`'s arguments. -/
theorem aadEntry_ok {s : State} (hW : Covers [⟨s.gpr .a5, 2560⟩] s.wr) (hal : (s.gpr .a5).toNat % 8 = 0) :
    WP isa (.block streamAadPre) s fun s' => Entered s (s.gpr .a5) s' ∧
      s'.gpr .s0 = s.gpr .a5 ∧ s'.gpr .s1 = s.gpr .a1 ∧ s'.gpr .s2 = s.gpr .a0 ∧
      s'.gpr .s4 = s.gpr .a3 ∧ s'.gpr .s5 = s.gpr .a4 ∧
      s'.gpr .s6 = BitVec.ofNat 64 ((s.gpr .a2).toNat % 16) := by
  refine WP.block_append (WP.mono (save_ok (b := .a5) hW hal) fun s₁ ⟨hg, h31, hk, hsv, hf⟩ => ?_)
  have e3 : s₁.gpr .a0 = s.gpr .a0 := hg _ (by decide)
  have e4 : s₁.gpr .a1 = s.gpr .a1 := hg _ (by decide)
  have e5 : s₁.gpr .a2 = s.gpr .a2 := hg _ (by decide)
  have e6 : s₁.gpr .a3 = s.gpr .a3 := hg _ (by decide)
  have e7 : s₁.gpr .a4 = s.gpr .a4 := hg _ (by decide)
  crun [Int.reduceNatCast', mov, e3, e4, e5, e6, e7, h31, and15]
  exact ⟨⟨hk.rd, hk.wr, hk.sp⟩, hsv, hf⟩

/-- The regions `stream_aad` writes. -/
abbrev aadFrame (St W sp : Addr) : List Region := savedR W :: absFrame St W 16 sp

/-- After the entry: `absorb`'s precondition, for additional data `x` so far
of `aad_len` bytes modulo 16. -/
theorem aad_entry {s : State} (hs : streamAadRISCV64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .a2).toNat % 16) :
    WP isa (.block streamAadPre) s fun s₁ => Entered s (s.gpr .a5) s₁ ∧ s₁.gpr .s2 = s.gpr .a0 ∧
      s₁.gpr .s1 = s.gpr .a1 ∧ s₁.gpr .s0 = s.gpr .a5 ∧
      AbsIn s₁.gpr s.sp 16 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x (s.gpr .a3) (s.gpr .a4).toNat s₁ ∧
      bytesAt s₁.mem (s.gpr .a3) (s.gpr .a4).toNat = bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat := by
  simp only [streamAadRISCV64] at hs
  obtain ⟨hrd, hwr, dcs, dcw, dds, ddw, dsw, wc, wd, ws, ww, hstk, -, -, hal⟩ := hs
  generalize hCtx : s.gpr .a0 = Ctx at *
  generalize hSt : s.gpr .a1 = St at *
  generalize hD : s.gpr .a3 = D at *
  generalize hn : (s.gpr .a4).toNat = n at *
  generalize hW : s.gpr .a5 = W at *
  have hlt : n < 2 ^ 64 := hn ▸ (s.gpr .a4).isLt
  have hn' : s.gpr .a4 = BitVec.ofNat 64 n := by rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hWc : Covers [⟨W, 2560⟩] s.wr := by rw [hwr]; exact covers_mem (by simp)
  refine WP.mono (aadEntry_ok (by rw [hW]; exact hWc) (by rw [hW]; exact hal)) fun s₁ ⟨en, h31, h30, h29, h24, h25, h26⟩ => ?_
  rw [hW] at en h31
  rw [hSt] at h30
  rw [hCtx] at h29
  rw [hD] at h24
  rw [hn'] at h25
  have perm : Perm Ctx St W s₁ :=
    (⟨covers_mem (by rw [hrd, hwr]; simp), covers_mem (by rw [hwr]; simp), hWc⟩ : Perm Ctx St W s).of_eq
      en.keeps.rd en.keeps.wr
  have hk : StkOk Ctx St W s.sp := hstk.stk (by simp) (by simp) (by simp)
  have he : Env s₁.gpr s.sp s₁ :=
    ⟨fun _ _ => rfl, en.keeps.sp, by rw [h29, h30, h31]; exact perm, by rw [h29, h30, h31, en.keeps.sp]; exact hk⟩
  have sW : Region.Sub (savedR W) ⟨W, 2560⟩ := Offset.sub_base _ (by decide)
  have hdat : bytesAt s₁.mem D n = bytesAt s.mem D n :=
    bytesAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ddw.sub_right sW) (by omega_using [hn])
  have hH : blockAt s₁.mem (s₁.gpr .s2 + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx := by
    rw [h29, ctxH_eq]
    exact blockAt_frame en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dcw.sub_left (Offset.sub_base _ (by decide))).sub_right sW)
  refine ⟨en, h29, h30, h31, ⟨he, h24, h25, by rw [h26, hx], ?_, hH⟩, hdat⟩
  rw [h30, h31]
  exact ⟨by rw [en.keeps.rd, en.keeps.wr, hrd]; exact covers_mem (by simp), hlt, wd, dds, ddw,
    by rw [en.keeps.sp]; exact hstk.buf (by simp)⟩

/-- One run of `stream_aad`, for additional data `x` so far of `aad_len` bytes
modulo 16. -/
theorem aad_run [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (hs : streamAadRISCV64.pre s) {x : List Byte}
    (hx : x.length % 16 = (s.gpr .a2).toNat % 16) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧
      (Absorbed s.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x →
        Absorbed s'.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
          (Spec.Gcm.ctxH s.mem (s.gpr .a0)) (x ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)) ∧
      Frame (aadFrame (s.gpr .a1) (s.gpr .a5) s.sp) s.mem s'.mem := by
  have hs' := hs
  obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, hstk, a0, a1, a5⟩ := hs'
  have L₀ : Lay (s.gpr .a0) (s.gpr .a1) (s.gpr .a5) := Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  refine WP.seq (WP.mono (aad_entry hs hx) fun s₁ ⟨en, h29, h30, h31, hIn, hdat⟩ => ?_)
  have dS : ∀ (d k : Nat), d + k ≤ 80 →
      (⟨s.gpr .a1 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (savedR (s.gpr .a5)) :=
    fun d k h => L₀.st_w h (.inr ⟨by decide, by decide⟩)
  have hA : ∀ (m : Mem), Frame [savedR (s.gpr .a5)] s.mem m →
      Absorbed s.mem (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x →
      Absorbed m (s.gpr .a1 + BitVec.ofNat 64 16) (s.gpr .a1 + BitVec.ofNat 64 32)
        (Spec.Gcm.ctxH s.mem (s.gpr .a0)) x :=
    fun m hf ha => ha.congr (blockAt_frame hf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dS 16 16 (by decide))
      (bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dS 32 16 (by decide)).sub_left (Region.sub_prefix (Nat.le_of_lt (Nat.mod_lt _ (by decide)))))
        (by omega_using []))
  refine WP.seq (WP.mono (absorb_ok (L₀.v h29 h30 h31) (.inr rfl) hIn) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  rw [h30, h31] at f₂
  have hk := h₂.env.stk'
  rw [h29, h30, h31] at hk
  have hsv : SavedAt s₂.mem (s.gpr .a5) s := en.saved.frame f₂ (saved_absFrame L₀ (.inr rfl) hk)
  have e31 : s₂.gpr .s0 = s.gpr .a5 := (h₂.env.fr _ (by decide)).trans h31
  refine WP.mono (restore_ok e31 a5 (by
      have := h₂.env.perm.w; rw [h31] at this; exact Covers.right this) hsv h₂.env.sp)
    fun s' ⟨ga, hm, _⟩ => ⟨ga, fun ha => ?_, ?_⟩
  · have := h₂.abs
    rw [h30, hdat] at this
    rw [hm]; exact this (hA _ en.frame ha)
  · rw [hm]
    exact (en.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)

theorem streamAad_wp [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (hs : streamAadRISCV64.pre s) :
    WP isa streamAad s fun s' => abiPreserved s s' ∧ streamAadRISCV64.post s s' := by
  have hz : (Spec.Gcm.zeros ((s.gpr .a2).toNat % 16)).length % 16 = (s.gpr .a2).toNat % 16 := by
    rw [Proof.Gcm.length_zeros, Nat.mod_mod]
  refine WP.mono (WP.forall_det (P := fun (i : (Block → Block) × List Byte × List Byte) =>
      StreamRepr s.mem (s.gpr .a1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) i.2.1 i.2.2 [] ∧
        s.gpr .a2 = BitVec.ofNat 64 i.2.2.length)
    (Q := fun i s' => StreamRepr s'.mem (s.gpr .a1) i.1 (Spec.Gcm.ctxH s.mem (s.gpr .a0)) i.2.1
      (i.2.2 ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) [])
    (aad_run hs hz) fun ⟨ciph, iv, a⟩ ⟨hr, hl⟩ => ?_) fun s' ⟨⟨ga, _, _⟩, h⟩ =>
      ⟨ga, fun ciph iv a hr hl => h ⟨ciph, iv, a⟩ ⟨hr, hl⟩⟩
  have hx : a.length % 16 = (s.gpr .a2).toNat % 16 := by rw [hl, toNat_mod16]
  obtain ⟨hj, ha, hc⟩ := Proof.Gcm.streamRepr_iff.mp hr
  have hs' := hs
  simp only [streamAadRISCV64] at hs'
  obtain ⟨-, -, -, -, -, -, dsw, -, -, ws, ww, hstk, -, -, -⟩ := hs'
  have dSt : ∀ r ∈ aadFrame (s.gpr .a1) (s.gpr .a5) s.sp, ∀ d, d + 16 ≤ 80 → (d + 16 ≤ 16 ∨ 48 ≤ d) →
      (⟨s.gpr .a1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro r hr d hd hd'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have st_off : ∀ e k, e + k ≤ 80 → (d + 16 ≤ e ∨ e + k ≤ d) →
        (⟨s.gpr .a1 + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint ⟨s.gpr .a1 + BitVec.ofNat 64 e, k⟩ :=
      fun e k he h => Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he])
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact st_off 16 16 (by decide) (by omega_using [hd'])
    · exact st_off 32 16 (by decide) (by omega_using [hd'])
    · exact (dsw.sub_left (Offset.sub_base _ (by omega_using [hd]))).sub_right (Offset.sub_base _ (by decide))
    · exact (hstk.buf (r := ⟨s.gpr .a1, 80⟩) (by simp)).sub_left (Offset.sub_base _ (by omega_using [hd]))
  refine WP.mono (aad_run hs hx) fun s' ⟨_, habs, hf⟩ => ?_
  refine Proof.Gcm.streamRepr_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [← hj]
    have := blockAt_frame hf fun r hr => by simpa using dSt r hr 0 (by decide) (.inl (by decide))
    simpa using this
  · exact habs ha
  · refine hc.congr ?_ ?_
    · exact blockAt_frame hf fun r hr => dSt r hr 48 (by decide) (.inr (by decide))
    · exact blockAt_frame hf fun r hr => dSt r hr 64 (by decide) (.inr (by decide))

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments; then `j0` (`j0_ct`) or `absorb 16`
(`absorb_ct`) from the invariants the entry's correctness gives; then the
exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem streamInitPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (.block streamInitPre) h).isSome = true := ⟨_, by taint_decide⟩

theorem streamAadPre_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (.block streamAadPre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem streamInit_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamInitRISCV64.pre streamInitRISCV64.pub streamInit := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a3, a4⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a3 a4
  let I₀ : State → Prop := fun s => streamInitRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    qsp.symm⟩, ?_⟩
  refine CT.seq (J := J0I (σ₁.gpr .a0) (σ₁.gpr .a3) (σ₁.gpr .a4) σ₁.sp (σ₁.gpr .a1) (σ₁.gpr .a2).toNat) ?_
    (fun s ⟨hs, e3, e4, e5, e6, e7, esp⟩ => WP.mono (si_entry hs) fun s₁ ⟨_, h29, h30, h31, hJ, _⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamInitPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7]⟩) hc
  · rw [e3] at h29
    rw [e6] at h30
    rw [e7] at h31
    rw [e3, e4, e5, esp] at hJ
    exact ⟨s₁.gpr, _, h29, h30, h31, hJ⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a4 ∧ s.sp = σ₁.sp) (j0_ct L)
    (fun s ⟨V, H, h29, h30, h31, hJ⟩ => WP.mono (j0_ok (L.v h29 h30 h31) hJ) fun s₂ h₂ =>
      ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a4) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamAad_ct [VG.Proof.Gcm.RISCV64.GhashLaw] : ConstantTime isa streamAadRISCV64.pre streamAadRISCV64.pub streamAad := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q3, q4, q5, q6, q7, q8, qsp⟩ := hq
  have L : Lay (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) := by
    obtain ⟨-, -, dcs, dcw, -, -, dsw, wc, -, ws, ww, -, a0, a1, a5⟩ := h₁
    exact Lay.of wc ws ww dcs dcw dsw a0 a1 a5
  let q := (σ₁.gpr .a2).toNat % 16
  have hq16 : q < 16 := Nat.mod_lt _ (by decide)
  let I₀ : State → Prop := fun s => streamAadRISCV64.pre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧
    s.gpr .a1 = σ₁.gpr .a1 ∧ s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧
    s.gpr .a5 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm,
    q8.symm, qsp.symm⟩, ?_⟩
  refine CT.seq (J := AbsI (σ₁.gpr .a0) (σ₁.gpr .a1) (σ₁.gpr .a5) σ₁.sp 16 (σ₁.gpr .a3) (σ₁.gpr .a4).toNat q)
    ?_ (fun s ⟨hs, e3, e4, e5, e6, e7, e8, esp⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := streamAadPre_taint
    exact CT.taintEq (I := I₀) _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8]⟩) hc
  · have hx : (List.replicate q (0 : Byte)).length % 16 = (s.gpr .a2).toNat % 16 := by
      rw [List.length_replicate, e5, Nat.mod_mod]
    refine WP.mono (aad_entry hs hx) fun s₁ ⟨_, h29, h30, h31, hIn, _⟩ => ?_
    rw [e3] at h29 hIn
    rw [e4] at h30
    rw [e8] at h31
    rw [e6, e7, esp] at hIn
    exact ⟨s₁.gpr, _, _, h29, h30, h31, by rw [List.length_replicate, Nat.mod_mod], hIn⟩
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a5 ∧ s.sp = σ₁.sp) (absorb_ct L (.inr rfl) hq16)
    (fun s ⟨V, H, x, h29, h30, h31, _, hs⟩ => WP.mono (absorb_ok (L.v h29 h30 h31) (.inr rfl) hs)
      fun s₂ h₂ => ⟨(h₂.env.fr _ (by decide)).trans h31, h₂.env.sp⟩) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a5) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-! ### `AesGcm.RISCV64.CTCryptFn`, which only this module used -/

section

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean. The entry by the taint
analysis from the public arguments, which it keeps in registers the pieces
preserve (`DI`); then `crypt` (`crypt_ct`) and `textAbsorb`
(`textAbsorb_ct`), in either order, from the invariants their correctness
gives; then the exit from `W`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- After the entry: the arguments kept, `len` (`N`) bytes at `data` (`D`),
after `aad_len` (`A`) bytes of additional data and `text_len` (`T`) of
text, and `R` rounds. -/
def DI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V : Reg → BitVec 64, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧
    V .s11 = T ∧ V .s3 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ Env V sp s ∧ DataW c st w s D N.toNat

/-- Before `crypt`, with the arguments kept. -/
def CI (c st w sp D : Addr) (R : Nat) (N A T : BitVec 64) (s : State) : Prop :=
  ∃ V icb P, V .s2 = c ∧ V .s1 = st ∧ V .s0 = w ∧ V .s9 = D ∧ V .s8 = N ∧ V .s10 = A ∧ V .s11 = T ∧
    P % 16 = T.toNat % 16 ∧ CrIn false V sp R icb P D D N.toNat s

theorem cryptEntry_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) (.block cryptEntry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cryptEntryArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]) (.block (cryptEntry ++ textArgs)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem textArgs_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s9, .s11])
    (.block textArgs) h).isSome = true := ⟨_, by taint_decide⟩

/-- The entry. -/
theorem sc_DI {s₀ : State} (h : streamCryptPre s₀) :
    WP isa (.block cryptEntry) s₀ (DI (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a7) s₀.sp (s₀.gpr .a5)
      (s₀.gpr .a1).toNat (s₀.gpr .a6) (s₀.gpr .a3) (s₀.gpr .a4)) :=
  WP.mono (sc1_wp (sc_W h) (sc_al h)) fun s₁ h1 => ⟨s₁.gpr, h1.s2, h1.s1, h1.s0, h1.s9, h1.s8, h1.s10, h1.s11,
    by rw [h1.s3, BitVec.ofNat_toNat, BitVec.setWidth_eq], sc_R h, sc_env h h1,
    sc_dataW h h1.en.keeps.wr h1.en.keeps.sp⟩

section
variable {c st w sp D : Addr} {R : Nat} {N A T : BitVec 64}

theorem di_ta {s : State} (h : DI c st w sp D R N A T s) : TA c st w sp D N A T s :=
  let ⟨V, h29, h30, h31, h20, h19, h22, h23, _, _, he, hd⟩ := h
  ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd.ok⟩

theorem ci_cr {s : State} (h : CI c st w sp D R N A T s) : CrI false c st w sp R D D N.toNat (T.toNat % 16) s :=
  let ⟨V, icb, P, h29, h30, h31, _, _, _, _, hP, ci⟩ := h
  ⟨V, icb, P, h29, h30, h31, hP, ci⟩

theorem ta_exit {s : State} (h : TA c st w sp D N A T s) : s.gpr .s0 = w ∧ s.sp = sp :=
  let ⟨_, _, _, h31, _, _, _, _, he, _⟩ := h
  ⟨(he.fr _ (by decide)).trans h31, he.sp⟩

/-- The arguments of `crypt`. -/
theorem di_textArgs {s : State} (h : DI c st w sp D R N A T s) :
    WP isa (.block textArgs) s (CI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono textArgs_ok fun s₂ ⟨h24, h25, h26, hg, hk⟩ => ?_
  have he₂ := he.keep (fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk.sp hk.rd hk.wr
  exact ⟨V, 0, T.toNat, h29, h30, h31, h20, h19, h22, h23, rfl, he₂, by rw [h24, he.fr _ (by decide), h20],
    by rw [h25, he.fr _ (by decide), h19, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [h26, he.fr _ (by decide), h23], h28, hR, by rw [h29, h30, h31]; exact hd.of_eq hk.rd hk.wr hk.sp,
    by rw [h30, h31]; exact (hd.of_eq hk.rd hk.wr hk.sp).ok, rfl, Bool.noConfusion⟩

variable (L : Lay c st w)
include L

theorem ci_crypt {s : State} (h : CI c st w sp D R N A T s) : WP isa crypt s (TA c st w sp D N A T) := by
  obtain ⟨V, icb, P, h29, h30, h31, h20, h19, h22, h23, _, ci⟩ := h
  refine WP.mono (WP.with_rdwr (crypt_ok (L.v h29 h30 h31) ci)) fun s' ⟨co, rd, wr, sp'⟩ =>
    ⟨V, h29, h30, h31, h20, h19, h22, h23, co.env, ?_⟩
  have := ci.data.ok.of_eq rd wr sp'
  rw [h30, h31] at this
  exact this

theorem di_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : DI c st w sp D R N A T s) :
    WP isa textAbsorb s (DI c st w sp D R N A T) := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, he, hd⟩ := h
  refine WP.mono (WP.with_rdwr (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd.ok) (by simp [h22])
    (by simp [h23]))) fun s' ⟨ta, rd, wr, sp'⟩ => ⟨V, h29, h30, h31, h20, h19, h22, h23, h28, hR, ta.env,
      hd.of_eq rd wr sp'⟩

theorem ta_textAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {s : State} (h : TA c st w sp D N A T s) :
    WP isa textAbsorb s fun s' => s'.gpr .s0 = w ∧ s'.sp = sp := by
  obtain ⟨V, h29, h30, h31, h20, h19, h22, h23, he, hd⟩ := h
  exact WP.mono (textAbsorb_ok (L.v h29 h30 h31) (a := List.replicate (A.toNat % 16) 0)
    (ct := List.replicate T.toNat 0) he rfl (by rw [h20, h19, h30, h31]; exact hd) (by simp [h22])
    (by simp [h23])) fun s' ta => ⟨(ta.env.fr _ (by decide)).trans h31, ta.env.sp⟩

end

/-- The invariant of the entry, from the public arguments of `σ`. -/
abbrev SCI (σ : State) (s : State) : Prop :=
  streamCryptPre s ∧ s.gpr .a0 = σ.gpr .a0 ∧ s.gpr .a1 = σ.gpr .a1 ∧ s.gpr .a2 = σ.gpr .a2 ∧
    s.gpr .a3 = σ.gpr .a3 ∧ s.gpr .a4 = σ.gpr .a4 ∧ s.gpr .a5 = σ.gpr .a5 ∧ s.gpr .a6 = σ.gpr .a6 ∧
    s.gpr .a7 = σ.gpr .a7 ∧ s.sp = σ.sp

theorem sci_of {σ₁ σ₂ : State} (h₁ : streamCryptPre σ₁) (h₂ : streamCryptPre σ₂) (hq : streamCryptPub σ₁ σ₂) :
    SCI σ₁ σ₁ ∧ SCI σ₁ σ₂ := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp⟩ := hq
  exact ⟨⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨h₂, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm⟩⟩

theorem sci_DI {σ s : State} (h : SCI σ s) :
    WP isa (.block cryptEntry) s (DI (σ.gpr .a0) (σ.gpr .a2) (σ.gpr .a7) σ.sp (σ.gpr .a5)
      (σ.gpr .a1).toNat (σ.gpr .a6) (σ.gpr .a3) (σ.gpr .a4)) := by
  obtain ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ := h
  have := sc_DI hs
  rw [e3, e4, e5, e6, e7, e8, e9, e10, esp] at this
  exact this

theorem streamEncrypt_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamEncryptRISCV64.pre streamEncryptRISCV64.pub streamEncrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := CI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a5) (σ₁.gpr .a1).toNat
    (σ₁.gpr .a6) (σ₁.gpr .a3) (σ₁.gpr .a4)) ?_
    (fun s h => WP.block_append (WP.mono (sci_DI h) fun _ h' => di_textArgs h')) ?_
  · obtain ⟨_, hc⟩ := cryptEntryArgs_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  refine CT.seq (J := fun s => s.gpr .s0 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp) (textAbsorb_ct L)
    (fun _ h => ta_textAbsorb L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

theorem streamDecrypt_ct [VG.Proof.Gcm.RISCV64.GhashLaw] :
    ConstantTime isa streamDecryptRISCV64.pre streamDecryptRISCV64.pub streamDecrypt := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have h₁' : streamCryptPre σ₁ := h₁
  have L := scLay h₁'
  obtain ⟨i₁, i₂⟩ := sci_of h₁' h₂ hq
  refine ⟨SCI σ₁, i₁, i₂, ?_⟩
  refine CT.seq (J := DI (σ₁.gpr .a0) (σ₁.gpr .a2) (σ₁.gpr .a7) σ₁.sp (σ₁.gpr .a5) (σ₁.gpr .a1).toNat
    (σ₁.gpr .a6) (σ₁.gpr .a3) (σ₁.gpr .a4)) ?_ (fun s h => sci_DI h) ?_
  · obtain ⟨_, hc⟩ := cryptEntry_taint
    exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, e3, e4, e5, e6, e7, e8, e9, e10, esp⟩ =>
      ⟨esp, by simp [e3, e4, e5, e6, e7, e8, e9, e10]⟩) hc
  refine CT.seq ((textAbsorb_ct L).mono fun _ h => di_ta h) (fun _ h => di_textAbsorb L h) ?_
  refine CT.seq ?_ (fun _ h => di_textArgs h) ?_
  · obtain ⟨_, hc⟩ := textArgs_taint
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, a20, a19, _, a23, _, _, e₁, _⟩
      ⟨_, _, _, _, b20, b19, _, b23, _, _, e₂, _⟩ => ⟨e₁.sp.trans e₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a19, b19]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a20, b20]
    · rw [e₁.fr _ (by decide), e₂.fr _ (by decide), a23, b23]
  refine CT.seq ((crypt_ct L).mono fun _ h => ci_cr h) (fun _ h => ci_crypt L h) ?_
  obtain ⟨_, hc⟩ := restore_taint
  exact CT.taintEq _ (fun _ => σ₁.gpr .a7) σ₁.sp (fun s h => ⟨(ta_exit h).2, by simp [(ta_exit h).1]⟩) hc

end VG.Proof.AesGcm.RISCV64

end

end

/-!
# AES-GCM on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with the 2048 bytes of stack `vg_ghash`'s
frame takes (but for `init`, which does not call it).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' :=
  init_wp hs

theorem streamInit_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamInitRISCV64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ streamInitRISCV64.post s s' :=
  streamInit_wp hs

theorem streamAad_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamAadRISCV64.pre s) :
    ∃ t s', Exec isa streamAad s t s' ∧ abiPreserved s s' ∧ streamAadRISCV64.post s s' :=
  streamAad_wp hs

theorem streamEncrypt_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamEncryptRISCV64.pre s) :
    ∃ t s', Exec isa streamEncrypt s t s' ∧ abiPreserved s s' ∧ streamEncryptRISCV64.post s s' :=
  streamEncrypt_wp hs

theorem streamDecrypt_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamDecryptRISCV64.pre s) :
    ∃ t s', Exec isa streamDecrypt s t s' ∧ abiPreserved s s' ∧ streamDecryptRISCV64.post s s' :=
  streamDecrypt_wp hs

theorem streamFinish_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamFinishRISCV64.pre s) :
    ∃ t s', Exec isa streamFinish s t s' ∧ abiPreserved s s' ∧ streamFinishRISCV64.post s s' :=
  streamFinish_wp hs

theorem streamVerify_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : streamVerifyRISCV64.pre s) :
    ∃ t s', Exec isa streamVerify s t s' ∧ abiPreserved s s' ∧ streamVerifyRISCV64.post s s' :=
  streamVerify_wp hs

theorem seal_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions (with empty buffers) -/

def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

def streamInitSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a3 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamAadSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a3 => 0x2000 | .a5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

def streamCryptSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x2000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩, ⟨0x4000, 2560⟩]

def finSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x5000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2560⟩]

def verSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x3000 | .a5 => 0x5000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x5000, 0⟩]
  wr := [⟨0x3000, 80⟩, ⟨0x4000, 2560⟩]

/-! ## The shared contracts -/

theorem init_verified :
    Verified RISCV64.target init (Proof.AesGcm.initScratchContract RISCV64.abi) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre,
      Spec.Gcm.initPost, initRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [initSat] using initSat)

theorem streamInit_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamInit (Proof.AesGcm.streamInitScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamInit_correct streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig,
      Spec.Gcm.streamInitPost, streamInitRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamInitSat] using streamInitSat)

theorem streamAad_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamAad (Proof.AesGcm.streamAadScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamAad_correct streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig,
      Spec.Gcm.streamAadPost, streamAadRISCV64, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true]
      [streamAadSat] using streamAadSat)

theorem streamEncrypt_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamEncrypt_correct streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, streamEncryptRISCV64, streamCryptPre, streamCryptPreX,
      streamCryptPub, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [streamCryptSat] using streamCryptSat)

theorem streamDecrypt_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamDecrypt_correct streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig,
      Spec.Gcm.streamTextPre, Proof.AesGcm.streamDecryptRoundsPost, streamDecryptRISCV64, streamCryptPre, streamCryptPreX,
      streamCryptPub, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [streamCryptSat] using streamCryptSat)

theorem streamFinish_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamFinish (Proof.AesGcm.streamFinishScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamFinish_correct streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Proof.AesGcm.streamFinishRoundsPost, streamFinishRISCV64, finPre, finPreX, rounds, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [finSat] using finSat)

theorem streamVerify_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target streamVerify (Proof.AesGcm.streamVerifyScratchContract RISCV64.abi 2048) :=
  Verified.of_correct streamVerify_correct streamVerify_ct (by
    sig_implies [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
      Spec.Gcm.streamVerifyPre, Proof.AesGcm.streamVerifyRoundsPost, streamVerifyRISCV64, verPre, verPreX, rounds, RISCV64.abi,
      RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true] [verSat] using verSat)

/-- `tag` at `0x5000` and the working space at `0x6000`, the stack arguments. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9009 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 2560⟩]

theorem seal_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target «seal» (Proof.AesGcm.sealScratchContract RISCV64.abi 2048) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Proof.AesGcm.sealRoundsPost, sealRISCV64, sealPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
      stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

/-- `tag` at `0x5000`, `tag_len` 0 and the working space at `0x6000`, the stack arguments. -/
def openSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low 32 bits
of `a0`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target «open» (Proof.AesGcm.openScratchContract RISCV64.abi 2048) :=
  Verified.of_correct open_correct open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openRISCV64, openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Proof.AesGcm.openRoundsPost, RISCV64.abi,
          RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
        simp only [openRISCV64] at h
        intro _
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openRISCV64,
          openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true, stackArg, stackArgAddr, List.getD,
          List.range, List.range.loop] at h
        obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
        refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_using [hi]) with rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
        · have e₁ : ¬((s₁.gpr .a1).toNat = 10 ∨ (s₁.gpr .a1).toNat = 12 ∨ (s₁.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .a1).toNat = 10 ∨ (s₂.gpr .a1).toNat = 12 ∨ (s₂.gpr .a1).toNat = 14) ↔ False :=
            ⟨fun x => x (h4 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
          openRISCV64, openPre, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs, stackBelow, stkOk, stkAll, and_true,
          stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
          [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

end VG.Proof.AesGcm.RISCV64

/-! ## With the working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it: the functions whose
arguments all arrive in registers in a frame of 2560 bytes, the working
space in the next register (`Verified.stackScratchL`); `seal` and `open`,
whose last arguments arrive on the stack, in a frame that copies them and
then passes the working space's address (`Verified.stackScratchArgs`).
-/

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract RISCV64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 init)
      (Spec.Gcm.initContract RISCV64.abi 2560) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre RISCV64.abi.ptrBits) (post := Spec.Gcm.initPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) init_verified (by decide) (by decide) (Proof.AesGcm.initPostOut_local _)
    initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { streamInitSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    RISCV64.abi, RISCV64.argRegs] [streamInitFrameSat, streamInitSat] using streamInitFrameSat

theorem streamInit_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 streamInit)
      (Spec.Gcm.streamInitContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamInit_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamInitPostOut_local _ vs m m₁ m₂ r hl)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { streamAadSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract RISCV64.abi 4608).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    RISCV64.abi, RISCV64.argRegs] [streamAadFrameSat, streamAadSat] using streamAadFrameSat

theorem streamAad_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 streamAad)
      (Spec.Gcm.streamAadContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamAad_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamAadPostOut_local _ vs m m₁ m₂ r hl)
    streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space. -/
def streamCryptFrameSat : State := { streamCryptSat with wr := [⟨0x3000, 80⟩, ⟨0x2000, 0⟩] }

theorem streamEncryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamEncryptRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamEncryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamEncryptRoundsPost, RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamEncrypt_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamEncrypt)
      (Proof.AesGcm.streamEncryptRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamEncrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamEncryptPostOut_local _ vs m m₁ m₂ r hl)
    streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Proof.AesGcm.streamDecryptRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamDecryptRoundsContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Proof.AesGcm.streamDecryptRoundsPost, RISCV64.abi, RISCV64.argRegs] [streamCryptFrameSat, streamCryptSat]
    using streamCryptFrameSat

theorem streamDecrypt_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamDecrypt)
      (Proof.AesGcm.streamDecryptRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamDecrypt_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamDecryptPostOut_local _ vs m m₁ m₂ r hl)
    streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without
the working space. -/
def finFrameSat : State := { finSat with wr := [⟨0x3000, 80⟩, ⟨0x5000, 16⟩] }

theorem finFrameSat_pre : ∃ s, (Proof.AesGcm.streamFinishRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamFinishRoundsContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre,
    Proof.AesGcm.streamFinishRoundsPost, RISCV64.abi, RISCV64.argRegs] [finFrameSat, finSat] using finFrameSat

theorem streamFinish_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 streamFinish)
      (Proof.AesGcm.streamFinishRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamFinishRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamFinish_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamFinishPostOut_local _ vs m m₁ m₂ r hl)
    finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without
the working space. -/
def verFrameSat : State := { verSat with wr := [⟨0x3000, 80⟩] }

theorem verFrameSat_pre : ∃ s, (Proof.AesGcm.streamVerifyRoundsContract RISCV64.abi 4608).pre s := by
  implies_sat [Proof.AesGcm.streamVerifyRoundsContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre,
    Proof.AesGcm.streamVerifyRoundsPost, RISCV64.abi, RISCV64.argRegs] [verFrameSat, verSat] using verFrameSat

theorem streamVerify_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 streamVerify)
      (Proof.AesGcm.streamVerifyRoundsContract RISCV64.abi 4608) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre RISCV64.abi.ptrBits)
    (post := Proof.AesGcm.streamVerifyRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 2048)
    (bytes := 2560) streamVerify_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.streamVerifyPostOut_local _ vs m m₁ m₂ r hl)
    verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: `tag` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x9000, 8⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcm.sealRoundsContract RISCV64.abi 4624).pre s := by
  implies_sat [Proof.AesGcm.sealRoundsContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Proof.AesGcm.sealRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

/-- `seal`, whose `tag` arrives on the stack: the frame copies it, then the
working space's address, above its stack pointer (`Verified.stackScratchArgs`). -/
theorem seal_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 «seal»)
      (Proof.AesGcm.sealRoundsContract RISCV64.abi 4624) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.sealPre RISCV64.abi.ptrBits) (post := Proof.AesGcm.sealRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2576) (m := 1) seal_verified (by decide) (by decide)
    (Proof.AesGcm.sealPre_local _) (Proof.AesGcm.sealPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.sealPostOut_local _ vs m m₁ m₂ r hl)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcm.openRoundsContract RISCV64.abi 4640).pre s := by
  implies_sat [Proof.AesGcm.openRoundsContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

/-- `open`, whose `tag` and `tag_len` arrive on the stack, as `seal`'s `tag` does. -/
theorem open_framed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Proof.AesGcm.openRoundsContract RISCV64.abi 4640) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Gcm.openPre RISCV64.abi.ptrBits) (post := Proof.AesGcm.openRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 2048) (bytes := 2592) (m := 2) (leak := some (Spec.Gcm.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesGcm.openPre_local _) (Proof.AesGcm.openPost_local _)
    (fun vs m m₁ m₂ r hl _ => Proof.AesGcm.openPostOut_local _ vs m m₁ m₂ r hl)
    openFrameSat_pre (hleak := Proof.AesGcm.openLeak_local _)

end VG.Proof.AesGcm.RISCV64
